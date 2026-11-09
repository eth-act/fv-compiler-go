import GoFV.Proof.Gen.G45
import GoFV.Proof.Witness.GenG44

namespace GoFV.Proof.Witness.GenG45

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/sort/Float64Slice.Swap,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "sort"
func "Float64Slice.Swap" 1 0 0
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
config localpkg "sort"
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
type t3 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t2 SLICE 24 8 8 hasptr,named "Float64Slice" "sort.Float64Slice" t3
type t4 INT 8 8 0 comparable,named "int" "int"
type t1 FUNC 8 8 8 hasptr,direct "method(Float64Slice) func(int, int)" "method(sort.Float64Slice) func(int, int)" 1 2 0
field 0 "x" t2 ? 0
field 1 "i" t4 ? 0
field 2 "j" t4 ? 0
aux a2 sym "sort.Float64Slice.Swap" "sort.Float64Slice.Swap" 1 - 0 - - - - 0
posbase p3 "sort/sort.go" 1 1 -1
aux a3 name "x" "x" PPARAM t2 0 1 used p3:145:7:0:0
aux a4 name "i" "i" PPARAM t4 24 1 used p3:145:28:0:0
aux a5 name "j" "j" PPARAM t4 32 1 used p3:145:31:0:0
aux a1 call "AuxCall{sort.Float64Slice.Swap}" a2 1 3 0 8 40 5 0
abiparam in 0 t2 a3 0,1,2 0
abiparam in 1 t4 a4 3 24
abiparam in 2 t4 a5 4 32
type t5 BOOL 1 1 0 comparable,named "bool" "bool"
type t6 INT8 1 1 0 comparable,named "int8" "int8"
type t7 INT16 2 2 0 comparable,named "int16" "int16"
type t8 INT32 4 4 0 comparable,named "int32" "int32"
type t9 INT64 8 8 0 comparable,named "int64" "int64"
type t10 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t11 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t12 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t13 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t14 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t15 UINT 8 8 0 comparable,named "uint" "uint"
type t16 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t17 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t18 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t10
type t19 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t8
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t12
type t21 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t4
type t22 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t16
type t23 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t14
type t24 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t3
type t25 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t18
type t26 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t27 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t28 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t29 SSA ? ? ? - "mem" ""
type t30 SSA ? ? ? - "flags" ""
type t31 SSA ? ? ? - "void" ""
type t32 SSA 16 8 ? - "int128" ""
type t33 RESULTS ? ? ? - "mem" "" 1 t29
type t34 PTR 8 8 8 hasptr,direct,comparable "*Float64Slice" "*sort.Float64Slice" t2
aux a6 type "float64" t3
slot s1 a3 t2 0 - 0
slot s2 a4 t4 0 - 0
slot s3 a5 t4 0 - 0
f b1 t1 a1 49 9
typs Bool=t5,Int8=t6,Int16=t7,Int32=t8,Int64=t9,UInt8=t10,UInt16=t11,UInt32=t12,UInt64=t13,Int=t4,Float32=t14,Float64=t3,UInt=t15,Uintptr=t16,String=t17,BytePtr=t18,Int32Ptr=t19,UInt32Ptr=t20,IntPtr=t21,UintptrPtr=t22,Float32Ptr=t23,Float64Ptr=t24,BytePtrPtr=t25,Complex64=t26,Complex128=t27,UnsafePtr=t28,Mem=t29,Flags=t30,Void=t31,Int128=t32,ResultMem=t33
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t21 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p3:145:6:2:0 3 -
v v8 Arg t4 0 a4 p3:145:6:2:0 4 -
v v9 Arg t4 0 a5 p3:145:6:2:0 1 -
v v10 SliceLen t4 0 - p3:145:65:0:0 2 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 1 v7
v v15 PtrIndex t24 0 - p3:145:65:0:0 1 v14,v8
v v16 Copy t29 0 - p3:145:65:2:0 3 v1
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v16
v v18 Copy t2 0 - p3:145:59:2:0 3 v7
v v19 Copy t4 0 - p3:145:59:2:0 4 v9
v v20 SliceLen t4 0 - p3:145:59:0:0 2 v18
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v19,v20
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v12 Copy t29 0 - p3:145:65:2:0 1 v1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v12
b b4 If p3:145:46:0:0 1 0 - v31 b6:0,b7:0 b2:0
v v24 SlicePtr t24 0 - p3:145:59:0:0 1 v18
v v25 PtrIndex t24 0 - p3:145:59:0:0 1 v24,v19
v v26 Copy t29 0 - p3:145:59:2:0 3 v16
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v26
v v28 Copy t2 0 - p3:145:46:2:0 3 v18
v v29 Copy t4 0 - p3:145:46:2:0 3 v8
v v30 SliceLen t4 0 - p3:145:46:0:0 2 v28
v v31 IsInBounds t5 0 - p3:145:46:0:0 1 v29,v30
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v22 Copy t29 0 - p3:145:59:2:0 1 v16
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v19,v20,v22
b b6 If p3:145:52:0:0 1 0 - v42 b8:0,b9:0 b4:0
v v34 SlicePtr t24 0 - p3:145:46:0:0 1 v28
v v35 PtrIndex t24 0 - p3:145:46:0:0 1 v34,v29
v v36 Copy t29 0 - p3:145:56:2:0 1 v26
v v37 Store t29 0 a6 p3:145:56:0:0 2 v35,v27,v36
v v38 Copy t3 0 - p3:145:56:2:0 1 v17
v v39 Copy t2 0 - p3:145:52:2:0 2 v28
v v40 Copy t4 0 - p3:145:52:2:0 3 v19
v v41 SliceLen t4 0 - p3:145:52:0:0 2 v39
v v42 IsInBounds t5 0 - p3:145:52:0:0 1 v40,v41
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v32 Copy t29 0 - p3:145:46:2:0 1 v26
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v29,v30,v32
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v45 SlicePtr t24 0 - p3:145:52:0:0 1 v39
v v46 PtrIndex t24 0 - p3:145:52:0:0 1 v45,v40
v v47 Copy t29 0 - p3:145:56:2:0 1 v37
v v48 Store t29 0 a6 p3:145:56:0:0 1 v46,v38,v47
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v43 Copy t29 0 - p3:145:52:2:0 1 v37
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v40,v41,v43
names s1,s2,s3
named s1 v7,v18,v28,v39
named s2 v8,v29
named s3 v9,v19,v40
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev -
freeb -
dcllen 4
end
pass 1 "number lines"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t21 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p3:145:6:2:0 3 -
v v8 Arg t4 0 a4 p3:145:6:2:0 4 -
v v9 Arg t4 0 a5 p3:145:6:2:0 1 -
v v10 SliceLen t4 0 - p3:145:65:1:0 2 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 1 v7
v v15 PtrIndex t24 0 - p3:145:65:0:0 1 v14,v8
v v16 Copy t29 0 - p3:145:65:2:0 3 v1
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v16
v v18 Copy t2 0 - p3:145:59:2:0 3 v7
v v19 Copy t4 0 - p3:145:59:2:0 4 v9
v v20 SliceLen t4 0 - p3:145:59:0:0 2 v18
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v19,v20
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v12 Copy t29 0 - p3:145:65:2:0 1 v1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v12
b b4 If p3:145:46:0:0 1 0 - v31 b6:0,b7:0 b2:0
v v24 SlicePtr t24 0 - p3:145:59:0:0 1 v18
v v25 PtrIndex t24 0 - p3:145:59:0:0 1 v24,v19
v v26 Copy t29 0 - p3:145:59:2:0 3 v16
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v26
v v28 Copy t2 0 - p3:145:46:2:0 3 v18
v v29 Copy t4 0 - p3:145:46:2:0 3 v8
v v30 SliceLen t4 0 - p3:145:46:0:0 2 v28
v v31 IsInBounds t5 0 - p3:145:46:0:0 1 v29,v30
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v22 Copy t29 0 - p3:145:59:2:0 1 v16
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v19,v20,v22
b b6 If p3:145:52:0:0 1 0 - v42 b8:0,b9:0 b4:0
v v34 SlicePtr t24 0 - p3:145:46:0:0 1 v28
v v35 PtrIndex t24 0 - p3:145:46:0:0 1 v34,v29
v v36 Copy t29 0 - p3:145:56:2:0 1 v26
v v37 Store t29 0 a6 p3:145:56:0:0 2 v35,v27,v36
v v38 Copy t3 0 - p3:145:56:2:0 1 v17
v v39 Copy t2 0 - p3:145:52:2:0 2 v28
v v40 Copy t4 0 - p3:145:52:2:0 3 v19
v v41 SliceLen t4 0 - p3:145:52:0:0 2 v39
v v42 IsInBounds t5 0 - p3:145:52:0:0 1 v40,v41
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v32 Copy t29 0 - p3:145:46:2:0 1 v26
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v29,v30,v32
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v45 SlicePtr t24 0 - p3:145:52:0:0 1 v39
v v46 PtrIndex t24 0 - p3:145:52:0:0 1 v45,v40
v v47 Copy t29 0 - p3:145:56:2:0 1 v37
v v48 Store t29 0 a6 p3:145:56:0:0 1 v46,v38,v47
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v43 Copy t29 0 - p3:145:52:2:0 1 v37
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v40,v41,v43
names s1,s2,s3
named s1 v7,v18,v28,v39
named s2 v8,v29
named s3 v9,v19,v40
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev -
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache linestarts 3:145:145
dcllen 4
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 15 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t21 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p3:145:6:2:0 11 -
v v8 Arg t4 0 a4 p3:145:6:2:0 7 -
v v9 Arg t4 0 a5 p3:145:6:2:0 8 -
v v10 SliceLen t4 0 - p3:145:65:1:0 2 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 1 v7
v v15 PtrIndex t24 0 - p3:145:65:0:0 1 v14,v8
v v16 Copy t29 0 - p3:145:65:2:0 0 v1
v v17 Load t3 0 - p3:145:65:0:0 2 v15,v1
v v18 Copy t2 0 - p3:145:59:2:0 0 v7
v v19 Copy t4 0 - p3:145:59:2:0 0 v9
v v20 SliceLen t4 0 - p3:145:59:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v20
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v12 Copy t29 0 - p3:145:65:2:0 0 v1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 If p3:145:46:0:0 1 0 - v31 b6:0,b7:0 b2:0
v v24 SlicePtr t24 0 - p3:145:59:0:0 1 v7
v v25 PtrIndex t24 0 - p3:145:59:0:0 1 v24,v9
v v26 Copy t29 0 - p3:145:59:2:0 0 v1
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v28 Copy t2 0 - p3:145:46:2:0 0 v7
v v29 Copy t4 0 - p3:145:46:2:0 0 v8
v v30 SliceLen t4 0 - p3:145:46:0:0 2 v7
v v31 IsInBounds t5 0 - p3:145:46:0:0 1 v8,v30
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v22 Copy t29 0 - p3:145:59:2:0 0 v1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v20,v1
b b6 If p3:145:52:0:0 1 0 - v42 b8:0,b9:0 b4:0
v v34 SlicePtr t24 0 - p3:145:46:0:0 1 v7
v v35 PtrIndex t24 0 - p3:145:46:0:0 1 v34,v8
v v36 Copy t29 0 - p3:145:56:2:0 0 v1
v v37 Store t29 0 a6 p3:145:56:0:0 4 v35,v27,v1
v v38 Copy t3 0 - p3:145:56:2:0 0 v17
v v39 Copy t2 0 - p3:145:52:2:0 0 v7
v v40 Copy t4 0 - p3:145:52:2:0 0 v9
v v41 SliceLen t4 0 - p3:145:52:0:0 2 v7
v v42 IsInBounds t5 0 - p3:145:52:0:0 1 v9,v41
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v32 Copy t29 0 - p3:145:46:2:0 0 v1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v30,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v45 SlicePtr t24 0 - p3:145:52:0:0 1 v7
v v46 PtrIndex t24 0 - p3:145:52:0:0 1 v45,v9
v v47 Copy t29 0 - p3:145:56:2:0 0 v37
v v48 Store t29 0 a6 p3:145:56:0:0 1 v46,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v43 Copy t29 0 - p3:145:52:2:0 0 v37
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s1,s2,s3
named s1 v7,v7,v7,v7
named s2 v8,v8
named s3 v9,v9,v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev -
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache linestarts 3:145:145
dcllen 4
end
pass 3 "early deadcode"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 8 -
v v8 Arg t4 0 a4 p3:145:6:2:0 6 -
v v9 Arg t4 0 a5 p3:145:6:2:0 6 -
v v10 SliceLen t4 0 - p3:145:65:1:0 2 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 1 v7
v v15 PtrIndex t24 0 - p3:145:65:0:0 1 v14,v8
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v20 SliceLen t4 0 - p3:145:59:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v20
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 If p3:145:46:0:0 1 0 - v31 b6:0,b7:0 b2:0
v v24 SlicePtr t24 0 - p3:145:59:0:0 1 v7
v v25 PtrIndex t24 0 - p3:145:59:0:0 1 v24,v9
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v30 SliceLen t4 0 - p3:145:46:0:0 2 v7
v v31 IsInBounds t5 0 - p3:145:46:0:0 1 v8,v30
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v20,v1
b b6 If p3:145:52:0:0 1 0 - v42 b8:0,b9:0 b4:0
v v34 SlicePtr t24 0 - p3:145:46:0:0 1 v7
v v35 PtrIndex t24 0 - p3:145:46:0:0 1 v34,v8
v v37 Store t29 0 a6 p3:145:56:0:0 2 v35,v27,v1
v v41 SliceLen t4 0 - p3:145:52:0:0 2 v7
v v42 IsInBounds t5 0 - p3:145:52:0:0 1 v9,v41
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v30,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v45 SlicePtr t24 0 - p3:145:52:0:0 1 v7
v v46 PtrIndex t24 0 - p3:145:52:0:0 1 v45,v9
v v48 Store t29 0 a6 p3:145:56:0:0 1 v46,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v43,v47,v32,v40,v39,v38,v36,v22,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache linestarts 3:145:145
dcllen 4
end
pass 4 "short circuit"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 8 -
v v8 Arg t4 0 a4 p3:145:6:2:0 6 -
v v9 Arg t4 0 a5 p3:145:6:2:0 6 -
v v10 SliceLen t4 0 - p3:145:65:1:0 2 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 1 v7
v v15 PtrIndex t24 0 - p3:145:65:0:0 1 v14,v8
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v20 SliceLen t4 0 - p3:145:59:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v20
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 If p3:145:46:0:0 1 0 - v31 b6:0,b7:0 b2:0
v v24 SlicePtr t24 0 - p3:145:59:0:0 1 v7
v v25 PtrIndex t24 0 - p3:145:59:0:0 1 v24,v9
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v30 SliceLen t4 0 - p3:145:46:0:0 2 v7
v v31 IsInBounds t5 0 - p3:145:46:0:0 1 v8,v30
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v20,v1
b b6 If p3:145:52:0:0 1 0 - v42 b8:0,b9:0 b4:0
v v34 SlicePtr t24 0 - p3:145:46:0:0 1 v7
v v35 PtrIndex t24 0 - p3:145:46:0:0 1 v34,v8
v v37 Store t29 0 a6 p3:145:56:0:0 2 v35,v27,v1
v v41 SliceLen t4 0 - p3:145:52:0:0 2 v7
v v42 IsInBounds t5 0 - p3:145:52:0:0 1 v9,v41
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v30,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v45 SlicePtr t24 0 - p3:145:52:0:0 1 v7
v v46 PtrIndex t24 0 - p3:145:52:0:0 1 v45,v9
v v48 Store t29 0 a6 p3:145:56:0:0 1 v46,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v43,v47,v32,v40,v39,v38,v36,v22,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache linestarts 3:145:145
dcllen 4
end
pass 5 "decompose user"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 8 -
v v8 Arg t4 0 a4 p3:145:6:2:0 6 -
v v9 Arg t4 0 a5 p3:145:6:2:0 6 -
v v10 SliceLen t4 0 - p3:145:65:1:0 2 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 1 v7
v v15 PtrIndex t24 0 - p3:145:65:0:0 1 v14,v8
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v20 SliceLen t4 0 - p3:145:59:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v20
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 If p3:145:46:0:0 1 0 - v31 b6:0,b7:0 b2:0
v v24 SlicePtr t24 0 - p3:145:59:0:0 1 v7
v v25 PtrIndex t24 0 - p3:145:59:0:0 1 v24,v9
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v30 SliceLen t4 0 - p3:145:46:0:0 2 v7
v v31 IsInBounds t5 0 - p3:145:46:0:0 1 v8,v30
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v20,v1
b b6 If p3:145:52:0:0 1 0 - v42 b8:0,b9:0 b4:0
v v34 SlicePtr t24 0 - p3:145:46:0:0 1 v7
v v35 PtrIndex t24 0 - p3:145:46:0:0 1 v34,v8
v v37 Store t29 0 a6 p3:145:56:0:0 2 v35,v27,v1
v v41 SliceLen t4 0 - p3:145:52:0:0 2 v7
v v42 IsInBounds t5 0 - p3:145:52:0:0 1 v9,v41
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v30,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v45 SlicePtr t24 0 - p3:145:52:0:0 1 v7
v v46 PtrIndex t24 0 - p3:145:52:0:0 1 v45,v9
v v48 Store t29 0 a6 p3:145:56:0:0 1 v46,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v43,v47,v32,v40,v39,v38,v36,v22,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache linestarts 3:145:145
dcllen 4
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 8 -
v v8 Arg t4 0 a4 p3:145:6:2:0 6 -
v v9 Arg t4 0 a5 p3:145:6:2:0 6 -
v v10 SliceLen t4 0 - p3:145:65:1:0 2 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 1 v7
v v15 PtrIndex t24 0 - p3:145:65:0:0 1 v14,v8
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v20 SliceLen t4 0 - p3:145:59:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v20
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 If p3:145:46:0:0 1 0 - v31 b6:0,b7:0 b2:0
v v24 SlicePtr t24 0 - p3:145:59:0:0 1 v7
v v25 PtrIndex t24 0 - p3:145:59:0:0 1 v24,v9
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v30 SliceLen t4 0 - p3:145:46:0:0 2 v7
v v31 IsInBounds t5 0 - p3:145:46:0:0 1 v8,v30
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v20,v1
b b6 If p3:145:52:0:0 1 0 - v42 b8:0,b9:0 b4:0
v v34 SlicePtr t24 0 - p3:145:46:0:0 1 v7
v v35 PtrIndex t24 0 - p3:145:46:0:0 1 v34,v8
v v37 Store t29 0 a6 p3:145:56:0:0 2 v35,v27,v1
v v41 SliceLen t4 0 - p3:145:52:0:0 2 v7
v v42 IsInBounds t5 0 - p3:145:52:0:0 1 v9,v41
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v30,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v45 SlicePtr t24 0 - p3:145:52:0:0 1 v7
v v46 PtrIndex t24 0 - p3:145:52:0:0 1 v45,v9
v v48 Store t29 0 a6 p3:145:56:0:0 1 v46,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v43,v47,v32,v40,v39,v38,v36,v22,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache linestarts 3:145:145
dcllen 4
end
pass 7 "opt"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 8 -
v v8 Arg t4 0 a4 p3:145:6:2:0 6 -
v v9 Arg t4 0 a5 p3:145:6:2:0 6 -
v v10 SliceLen t4 0 - p3:145:65:1:0 2 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 1 v7
v v15 AddPtr t24 0 - p3:145:65:0:0 1 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v20 SliceLen t4 0 - p3:145:59:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v20
v v43 Mul64 t4 0 - p3:145:65:0:0 1 v8,v47
v v47 Const64 t4 8 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 If p3:145:46:0:0 1 0 - v31 b6:0,b7:0 b2:0
v v24 SlicePtr t24 0 - p3:145:59:0:0 1 v7
v v25 AddPtr t24 0 - p3:145:59:0:0 1 v24,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v30 SliceLen t4 0 - p3:145:46:0:0 2 v7
v v31 IsInBounds t5 0 - p3:145:46:0:0 1 v8,v30
v v32 Mul64 t4 0 - p3:145:59:0:0 1 v9,v40
v v40 Const64 t4 8 - p3:145:59:0:0 1 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v20,v1
b b6 If p3:145:52:0:0 1 0 - v42 b8:0,b9:0 b4:0
v v34 SlicePtr t24 0 - p3:145:46:0:0 1 v7
v v35 AddPtr t24 0 - p3:145:46:0:0 1 v34,v39
v v37 Store t29 0 a6 p3:145:56:0:0 2 v35,v27,v1
v v41 SliceLen t4 0 - p3:145:52:0:0 2 v7
v v42 IsInBounds t5 0 - p3:145:52:0:0 1 v9,v41
v v39 Mul64 t4 0 - p3:145:46:0:0 1 v8,v38
v v38 Const64 t4 8 - p3:145:46:0:0 1 -
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v30,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v45 SlicePtr t24 0 - p3:145:52:0:0 1 v7
v v46 AddPtr t24 0 - p3:145:52:0:0 1 v45,v36
v v48 Store t29 0 a6 p3:145:56:0:0 1 v46,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
v v36 Mul64 t4 0 - p3:145:52:0:0 1 v9,v22
v v22 Const64 t4 8 - p3:145:52:0:0 1 -
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache linestarts 3:145:145
dcllen 4
end
pass 8 "zero arg cse"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 8 -
v v8 Arg t4 0 a4 p3:145:6:2:0 6 -
v v9 Arg t4 0 a5 p3:145:6:2:0 6 -
v v10 SliceLen t4 0 - p3:145:65:1:0 2 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
v v47 Const64 t4 8 - p3:145:65:0:0 4 -
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 1 v7
v v15 AddPtr t24 0 - p3:145:65:0:0 1 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v20 SliceLen t4 0 - p3:145:59:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v20
v v43 Mul64 t4 0 - p3:145:65:0:0 1 v8,v47
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 If p3:145:46:0:0 1 0 - v31 b6:0,b7:0 b2:0
v v24 SlicePtr t24 0 - p3:145:59:0:0 1 v7
v v25 AddPtr t24 0 - p3:145:59:0:0 1 v24,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v30 SliceLen t4 0 - p3:145:46:0:0 2 v7
v v31 IsInBounds t5 0 - p3:145:46:0:0 1 v8,v30
v v32 Mul64 t4 0 - p3:145:59:0:0 1 v9,v47
v v40 Const64 t4 8 - p3:145:59:0:0 0 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v20,v1
b b6 If p3:145:52:0:0 1 0 - v42 b8:0,b9:0 b4:0
v v34 SlicePtr t24 0 - p3:145:46:0:0 1 v7
v v35 AddPtr t24 0 - p3:145:46:0:0 1 v34,v39
v v37 Store t29 0 a6 p3:145:56:0:0 2 v35,v27,v1
v v41 SliceLen t4 0 - p3:145:52:0:0 2 v7
v v42 IsInBounds t5 0 - p3:145:52:0:0 1 v9,v41
v v39 Mul64 t4 0 - p3:145:46:0:0 1 v8,v47
v v38 Const64 t4 8 - p3:145:46:0:0 0 -
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v30,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v45 SlicePtr t24 0 - p3:145:52:0:0 1 v7
v v46 AddPtr t24 0 - p3:145:52:0:0 1 v45,v36
v v48 Store t29 0 a6 p3:145:56:0:0 1 v46,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
v v36 Mul64 t4 0 - p3:145:52:0:0 1 v9,v47
v v22 Const64 t4 8 - p3:145:52:0:0 0 -
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache linestarts 3:145:145
dcllen 4
end
pass 9 "opt deadcode"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 8 -
v v8 Arg t4 0 a4 p3:145:6:2:0 6 -
v v9 Arg t4 0 a5 p3:145:6:2:0 6 -
v v10 SliceLen t4 0 - p3:145:65:1:0 2 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
v v47 Const64 t4 8 - p3:145:65:0:0 4 -
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 1 v7
v v15 AddPtr t24 0 - p3:145:65:0:0 1 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v20 SliceLen t4 0 - p3:145:59:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v20
v v43 Mul64 t4 0 - p3:145:65:0:0 1 v8,v47
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 If p3:145:46:0:0 1 0 - v31 b6:0,b7:0 b2:0
v v24 SlicePtr t24 0 - p3:145:59:0:0 1 v7
v v25 AddPtr t24 0 - p3:145:59:0:0 1 v24,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v30 SliceLen t4 0 - p3:145:46:0:0 2 v7
v v31 IsInBounds t5 0 - p3:145:46:0:0 1 v8,v30
v v32 Mul64 t4 0 - p3:145:59:0:0 1 v9,v47
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v20,v1
b b6 If p3:145:52:0:0 1 0 - v42 b8:0,b9:0 b4:0
v v34 SlicePtr t24 0 - p3:145:46:0:0 1 v7
v v35 AddPtr t24 0 - p3:145:46:0:0 1 v34,v39
v v37 Store t29 0 a6 p3:145:56:0:0 2 v35,v27,v1
v v41 SliceLen t4 0 - p3:145:52:0:0 2 v7
v v42 IsInBounds t5 0 - p3:145:52:0:0 1 v9,v41
v v39 Mul64 t4 0 - p3:145:46:0:0 1 v8,v47
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v30,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v45 SlicePtr t24 0 - p3:145:52:0:0 1 v7
v v46 AddPtr t24 0 - p3:145:52:0:0 1 v45,v36
v v48 Store t29 0 a6 p3:145:56:0:0 1 v46,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
v v36 Mul64 t4 0 - p3:145:52:0:0 1 v9,v47
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache linestarts 3:145:145
dcllen 4
end
pass 10 "generic cse"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 8 -
v v8 Arg t4 0 a4 p3:145:6:2:0 6 -
v v9 Arg t4 0 a5 p3:145:6:2:0 6 -
v v10 SliceLen t4 0 - p3:145:65:1:0 8 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 2 v8,v10
v v47 Const64 t4 8 - p3:145:65:0:0 4 -
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 4 v7
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v20 SliceLen t4 0 - p3:145:59:0:0 0 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 2 v9,v10
v v43 Mul64 t4 0 - p3:145:65:0:0 2 v47,v8
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 If p3:145:46:0:0 1 0 - v11 b6:0,b7:0 b2:0
v v24 SlicePtr t24 0 - p3:145:59:0:0 0 v7
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v14,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v30 SliceLen t4 0 - p3:145:46:0:0 0 v7
v v31 IsInBounds t5 0 - p3:145:46:0:0 0 v8,v10
v v32 Mul64 t4 0 - p3:145:59:0:0 2 v47,v9
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v10,v1
b b6 If p3:145:52:0:0 1 0 - v21 b8:0,b9:0 b4:0
v v34 SlicePtr t24 0 - p3:145:46:0:0 0 v7
v v35 AddPtr t24 0 - p3:145:46:0:0 0 v14,v43
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
v v41 SliceLen t4 0 - p3:145:52:0:0 0 v7
v v42 IsInBounds t5 0 - p3:145:52:0:0 0 v9,v10
v v39 Mul64 t4 0 - p3:145:46:0:0 0 v47,v8
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v10,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v45 SlicePtr t24 0 - p3:145:52:0:0 0 v7
v v46 AddPtr t24 0 - p3:145:52:0:0 0 v14,v32
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
v v36 Mul64 t4 0 - p3:145:52:0:0 0 v47,v9
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v10,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 11 "phiopt"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 8 -
v v8 Arg t4 0 a4 p3:145:6:2:0 6 -
v v9 Arg t4 0 a5 p3:145:6:2:0 6 -
v v10 SliceLen t4 0 - p3:145:65:1:0 8 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 2 v8,v10
v v47 Const64 t4 8 - p3:145:65:0:0 4 -
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 4 v7
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v20 SliceLen t4 0 - p3:145:59:0:0 0 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 2 v9,v10
v v43 Mul64 t4 0 - p3:145:65:0:0 2 v47,v8
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 If p3:145:46:0:0 1 0 - v11 b6:0,b7:0 b2:0
v v24 SlicePtr t24 0 - p3:145:59:0:0 0 v7
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v14,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v30 SliceLen t4 0 - p3:145:46:0:0 0 v7
v v31 IsInBounds t5 0 - p3:145:46:0:0 0 v8,v10
v v32 Mul64 t4 0 - p3:145:59:0:0 2 v47,v9
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v10,v1
b b6 If p3:145:52:0:0 1 0 - v21 b8:0,b9:0 b4:0
v v34 SlicePtr t24 0 - p3:145:46:0:0 0 v7
v v35 AddPtr t24 0 - p3:145:46:0:0 0 v14,v43
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
v v41 SliceLen t4 0 - p3:145:52:0:0 0 v7
v v42 IsInBounds t5 0 - p3:145:52:0:0 0 v9,v10
v v39 Mul64 t4 0 - p3:145:46:0:0 0 v47,v8
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v10,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v45 SlicePtr t24 0 - p3:145:52:0:0 0 v7
v v46 AddPtr t24 0 - p3:145:52:0:0 0 v14,v32
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
v v36 Mul64 t4 0 - p3:145:52:0:0 0 v47,v9
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v10,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 12 "gcse deadcode"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 2 -
v v8 Arg t4 0 a4 p3:145:6:2:0 4 -
v v9 Arg t4 0 a5 p3:145:6:2:0 4 -
v v10 SliceLen t4 0 - p3:145:65:1:0 6 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 2 v8,v10
v v47 Const64 t4 8 - p3:145:65:0:0 2 -
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 2 v7
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v21 IsInBounds t5 0 - p3:145:59:0:0 2 v9,v10
v v43 Mul64 t4 0 - p3:145:65:0:0 1 v47,v8
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 If p3:145:46:0:0 1 0 - v11 b6:0,b7:0 b2:0
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v14,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v32 Mul64 t4 0 - p3:145:59:0:0 1 v47,v9
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v10,v1
b b6 If p3:145:52:0:0 1 0 - v21 b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v10,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v10,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v36,v46,v45,v39,v42,v41,v35,v34,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 13 "nilcheckelim"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 2 -
v v8 Arg t4 0 a4 p3:145:6:2:0 4 -
v v9 Arg t4 0 a5 p3:145:6:2:0 4 -
v v10 SliceLen t4 0 - p3:145:65:1:0 6 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 2 v8,v10
v v47 Const64 t4 8 - p3:145:65:0:0 2 -
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 2 v7
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v21 IsInBounds t5 0 - p3:145:59:0:0 2 v9,v10
v v43 Mul64 t4 0 - p3:145:65:0:0 1 v47,v8
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 If p3:145:46:0:0 1 0 - v11 b6:0,b7:0 b2:0
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v14,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v32 Mul64 t4 0 - p3:145:59:0:0 1 v47,v9
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v10,v1
b b6 If p3:145:52:0:0 1 0 - v21 b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v10,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v10,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v36,v46,v45,v39,v42,v41,v35,v34,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 14 "prove"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 2 -
v v8 Arg t4 0 a4 p3:145:6:2:0 4 -
v v9 Arg t4 0 a5 p3:145:6:2:0 4 -
v v47 Const64 t4 8 - p3:145:65:0:0 2 -
v v10 SliceLen t4 0 - p3:145:65:1:0 6 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v10
v v43 Mul64 t4 0 - p3:145:65:0:0 1 v47,v8
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Mul64 t4 0 - p3:145:59:0:0 1 v47,v9
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v14,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v10,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v10,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v10,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v36,v46,v45,v39,v42,v41,v35,v34,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 15 "divisible"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 2 -
v v8 Arg t4 0 a4 p3:145:6:2:0 4 -
v v9 Arg t4 0 a5 p3:145:6:2:0 4 -
v v47 Const64 t4 8 - p3:145:65:0:0 2 -
v v10 SliceLen t4 0 - p3:145:65:1:0 6 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v10
v v43 Mul64 t4 0 - p3:145:65:0:0 1 v47,v8
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Mul64 t4 0 - p3:145:59:0:0 1 v47,v9
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v14,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v10,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v10,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v10,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v36,v46,v45,v39,v42,v41,v35,v34,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 16 "divmod"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 2 -
v v8 Arg t4 0 a4 p3:145:6:2:0 4 -
v v9 Arg t4 0 a5 p3:145:6:2:0 4 -
v v47 Const64 t4 8 - p3:145:65:0:0 2 -
v v10 SliceLen t4 0 - p3:145:65:1:0 6 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v10
v v43 Mul64 t4 0 - p3:145:65:0:0 1 v47,v8
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Mul64 t4 0 - p3:145:59:0:0 1 v47,v9
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v14,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v10,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v10,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v10,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v36,v46,v45,v39,v42,v41,v35,v34,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 17 "middle opt"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 2 -
v v8 Arg t4 0 a4 p3:145:6:2:0 4 -
v v9 Arg t4 0 a5 p3:145:6:2:0 4 -
v v10 SliceLen t4 0 - p3:145:65:1:0 6 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v10
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v14,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v10,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v10,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v10,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v47,v45,v39,v42,v41,v35,v34,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 18 "known bits"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 2 -
v v8 Arg t4 0 a4 p3:145:6:2:0 4 -
v v9 Arg t4 0 a5 p3:145:6:2:0 4 -
v v10 SliceLen t4 0 - p3:145:65:1:0 6 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v10
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v14,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v10,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v10,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v10,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v47,v45,v39,v42,v41,v35,v34,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 19 "early fuse"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p3:145:6:2:0 2 -
v v8 Arg t4 0 a4 p3:145:6:2:0 4 -
v v9 Arg t4 0 a5 p3:145:6:2:0 4 -
v v10 SliceLen t4 0 - p3:145:65:1:0 6 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v10
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v14,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v10,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v10,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v10,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v47,v45,v39,v42,v41,v35,v34,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 20 "expand calls"
aux a7 nameoff "i+0" a4 0
aux a8 nameoff "j+0" a5 0
aux a9 nameoff "x+0" a3 0
aux a10 nameoff "x+8" a3 8
aux a11 nameoff "x+16" a3 16
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 SliceMake t2 0 - p3:145:65:2:0 2 v42,v41,v35
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v10 SliceLen t4 0 - p3:145:65:1:0 6 v7
v v11 IsInBounds t5 0 - p3:145:65:0:0 1 v8,v10
v v47 SB t16 0 - p0:0:0:0:0 0 -
v v45 SP t16 0 - p0:0:0:0:0 2 -
v v39 OffPtr t34 0 - p0:0:0:0:0 0 v45
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 1 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 1 -
v v35 ArgIntReg t4 2 a11 p3:145:65:2:0 1 -
v v34 OffPtr t21 0 - p0:0:0:0:0 0 v45
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 SlicePtr t24 0 - p3:145:65:0:0 2 v7
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v10
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v14,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v10,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v14,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v10,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v10,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v10,v37
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v9
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts 0=v39,v34
freev v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 21 "decompose builtin"
slot s4 a3 t24 0 - 0
slot s5 a3 t4 8 - 0
slot s6 a3 t4 16 - 0
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 SliceMake t2 0 - p3:145:65:2:0 0 v42,v41,v35
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v11 IsInBounds t5 0 - p3:145:65:1:0 1 v8,v41
v v47 SB t16 0 - p0:0:0:0:0 0 -
v v45 SP t16 0 - p0:0:0:0:0 2 -
v v39 OffPtr t34 0 - p0:0:0:0:0 0 v45
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 3 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 7 -
v v35 ArgIntReg t4 2 a11 p3:145:65:2:0 1 -
v v34 OffPtr t21 0 - p0:0:0:0:0 0 v45
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v41
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v42,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v42,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s3,s2,s4,s5,s6
named s3 v9
named s2 v8
named s4 v42
named s5 v41
named s6 v35
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts 0=v39,v34
freev v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 22 "softfloat"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 SliceMake t2 0 - p3:145:65:2:0 0 v42,v41,v35
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v11 IsInBounds t5 0 - p3:145:65:1:0 1 v8,v41
v v47 SB t16 0 - p0:0:0:0:0 0 -
v v45 SP t16 0 - p0:0:0:0:0 2 -
v v39 OffPtr t34 0 - p0:0:0:0:0 0 v45
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 3 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 7 -
v v35 ArgIntReg t4 2 a11 p3:145:65:2:0 1 -
v v34 OffPtr t21 0 - p0:0:0:0:0 0 v45
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v41
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v42,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v42,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s3,s2,s4,s5,s6
named s3 v9
named s2 v8
named s4 v42
named s5 v41
named s6 v35
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts 0=v39,v34
freev v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 23 "branchelim"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v7 SliceMake t2 0 - p3:145:65:2:0 0 v42,v41,v35
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v11 IsInBounds t5 0 - p3:145:65:1:0 1 v8,v41
v v47 SB t16 0 - p0:0:0:0:0 0 -
v v45 SP t16 0 - p0:0:0:0:0 2 -
v v39 OffPtr t34 0 - p0:0:0:0:0 0 v45
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 3 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 7 -
v v35 ArgIntReg t4 2 a11 p3:145:65:2:0 1 -
v v34 OffPtr t21 0 - p0:0:0:0:0 0 v45
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v41
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v42,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v42,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s3,s2,s4,s5,s6
named s3 v9
named s2 v8
named s4 v42
named s5 v41
named s6 v35
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts 0=v39,v34
freev v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 24 "late opt"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v11 IsInBounds t5 0 - p3:145:65:1:0 1 v8,v41
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 2 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 6 -
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v41
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v42,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v42,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s3,s2,s4,s5,s6
named s3 v9
named s2 v8
named s4 v42
named s5 v41
named s6 v35
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v34,v35,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 25 "dead auto elim"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v11 IsInBounds t5 0 - p3:145:65:1:0 1 v8,v41
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 2 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 6 -
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v41
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v42,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v42,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s3,s2,s4,s5,s6
named s3 v9
named s2 v8
named s4 v42
named s5 v41
named s6 v35
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v34,v35,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 26 "sccp"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v11 IsInBounds t5 0 - p3:145:65:1:0 1 v8,v41
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 2 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 6 -
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v41
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v42,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 First p3:145:46:0:0 1 0 - - b6:0,b7:0 b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v42,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 First p3:145:52:0:0 1 0 - - b8:0,b9:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 2 v15,v27,v1
b b7 Exit p3:145:46:0:0 0 0 - v33 - b4:1
v v33 PanicBounds t29 0 - p3:145:46:0:0 1 v8,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b9 Exit p3:145:52:0:0 0 0 - v44 - b6:1
v v44 PanicBounds t29 0 - p3:145:52:0:0 1 v9,v41,v37
names s3,s2,s4,s5,s6
named s3 v9
named s2 v8
named s4 v42
named s5 v41
named s6 v35
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v34,v35,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b9,b6,b7,b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b4,b7:b4,b8:b6,b9:b6
cache sdom b1:-:b3:-:2:53,b2:b1:b5:-:11:50,b3:b1:-:b2:5:8,b4:b2:b7:-:20:47,b5:b2:-:b4:14:17,b6:b4:b9:-:29:44,b7:b4:-:b6:23:26,b8:b6:-:-:38:41,b9:b6:-:b8:32:35
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 27 "generic deadcode"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 3 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 3 -
v v11 IsInBounds t5 0 - p3:145:65:1:0 1 v8,v41
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 2 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
b b2 If p3:145:59:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v41
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v42,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 Plain p3:145:46:0:0 0 0 - - b6:0 b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v42,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 Plain p3:145:52:0:0 0 0 - - b8:0 b4:0
v v37 Store t29 0 a6 p3:145:56:0:0 1 v15,v27,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b6:0
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v44,v33,v34,v35,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b9,b7
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 28 "late fuse"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 3 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 3 -
v v11 IsInBounds t5 0 - p3:145:65:1:0 1 v8,v41
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 2 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
b b2 If p3:145:59:0:0 1 0 - v21 b8:0,b5:0 b1:0
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v41
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v42,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 BlockInvalid p3:145:46:0:0 0 0 - - - -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 BlockInvalid p3:145:52:0:0 0 0 - - - -
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v42,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
v v37 Store t29 0 a6 p3:145:56:0:0 1 v15,v27,v1
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v44,v33,v34,v35,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b9,b7
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 29 "check bce"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 3 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 3 -
v v11 IsInBounds t5 0 - p3:145:65:1:0 1 v8,v41
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 2 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
b b2 If p3:145:59:0:0 1 0 - v21 b8:0,b5:0 b1:0
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v41
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v42,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 BlockInvalid p3:145:46:0:0 0 0 - - - -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 BlockInvalid p3:145:52:0:0 0 0 - - - -
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v42,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
v v37 Store t29 0 a6 p3:145:56:0:0 1 v15,v27,v1
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v44,v33,v34,v35,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b9,b7
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 30 "dse"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 3 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 3 -
v v11 IsInBounds t5 0 - p3:145:65:1:0 1 v8,v41
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 2 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
b b2 If p3:145:59:0:0 1 0 - v21 b8:0,b5:0 b1:0
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v41
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v42,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 BlockInvalid p3:145:46:0:0 0 0 - - - -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 BlockInvalid p3:145:52:0:0 0 0 - - - -
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v42,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
v v37 Store t29 0 a6 p3:145:56:0:0 1 v15,v27,v1
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v44,v33,v34,v35,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b9,b7
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 31 "memcombine"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 3 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 3 -
v v11 IsInBounds t5 0 - p3:145:65:1:0 1 v8,v41
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 2 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
b b2 If p3:145:59:0:0 1 0 - v21 b8:0,b5:0 b1:0
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v41
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v42,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 BlockInvalid p3:145:46:0:0 0 0 - - - -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 BlockInvalid p3:145:52:0:0 0 0 - - - -
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v42,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
v v37 Store t29 0 a6 p3:145:56:0:0 1 v15,v27,v1
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v44,v33,v34,v35,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b9,b7
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 32 "writebarrier"
f b1 t1 a1 49 9
b b1 If p3:145:65:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 3 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 3 -
v v11 IsInBounds t5 0 - p3:145:65:1:0 1 v8,v41
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 2 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
b b2 If p3:145:59:0:0 1 0 - v21 b8:0,b5:0 b1:0
v v21 IsInBounds t5 0 - p3:145:59:0:0 1 v9,v41
v v43 Lsh64x64 t4 1 - p3:145:65:0:0 1 v8,v36
v v15 AddPtr t24 0 - p3:145:65:0:0 2 v42,v43
v v17 Load t3 0 - p3:145:65:0:0 1 v15,v1
v v36 Const64 t13 3 - p3:145:65:0:0 1 -
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 PanicBounds t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 BlockInvalid p3:145:46:0:0 0 0 - - - -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 PanicBounds t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 BlockInvalid p3:145:52:0:0 0 0 - - - -
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v32 Lsh64x64 t4 1 - p3:145:59:0:0 1 v9,v46
v v25 AddPtr t24 0 - p3:145:59:0:0 2 v42,v32
v v27 Load t3 0 - p3:145:59:0:0 1 v25,v1
v v46 Const64 t13 3 - p3:145:59:0:0 1 -
v v37 Store t29 0 a6 p3:145:56:0:0 1 v15,v27,v1
v v48 Store t29 0 a6 p3:145:56:0:0 1 v25,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v44,v33,v34,v35,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b9,b7
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 33 "lower"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 BlockInvalid p3:145:46:0:0 0 0 - - - -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 BlockInvalid p3:145:52:0:0 0 0 - - - -
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b9,b7
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 34 "addressing modes"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 BlockInvalid p3:145:46:0:0 0 0 - - - -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 BlockInvalid p3:145:52:0:0 0 0 - - - -
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b9,b7
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 35 "late lower"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 BlockInvalid p3:145:46:0:0 0 0 - - - -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 BlockInvalid p3:145:52:0:0 0 0 - - - -
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b9,b7
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 36 "pair"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b4 BlockInvalid p3:145:46:0:0 0 0 - - - -
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b6 BlockInvalid p3:145:52:0:0 0 0 - - - -
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b9,b7
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache auxmap a3:1,a4:2,a5:3,-:4
cache linestarts 3:145:145
dcllen 4
end
pass 38 "lowered cse"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b8:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b5:b2:-:b8:14:17,b8:b2:-:-:20:23
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
dcllen 4
end
pass 39 "elim unread autos"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b8:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b5:b2:-:b8:14:17,b8:b2:-:-:20:23
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
dcllen 4
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b8:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b5:b2:-:b8:14:17,b8:b2:-:-:20:23
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
dcllen 4
end
pass 41 "lowered deadcode"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b8:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b5:b2:-:b8:14:17,b8:b2:-:-:20:23
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
dcllen 4
end
pass 42 "checkLower"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b8:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b5:b2:-:b8:14:17,b8:b2:-:-:20:23
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
dcllen 4
end
pass 43 "loop invariant"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b8:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b5:b2:-:b8:14:17,b8:b2:-:-:20:23
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
dcllen 4
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b8:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b5:b2:-:b8:14:17,b8:b2:-:-:20:23
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
dcllen 4
end
pass 45 "tighten"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b8:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b5:b2:-:b8:14:17,b8:b2:-:-:20:23
cache loopnest 10 0 - -
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
dcllen 4
end
pass 46 "late deadcode"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b8:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b5:b2:-:b8:14:17,b8:b2:-:-:20:23
cache loopnest 10 0 - -
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
dcllen 4
end
pass 47 "critical"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b8:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b5:b2:-:b8:14:17,b8:b2:-:-:20:23
cache loopnest 10 0 - -
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
dcllen 4
end
pass 48 "phi tighten"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b8:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b5:b2:-:b8:14:17,b8:b2:-:-:20:23
cache loopnest 10 0 - -
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
dcllen 4
end
pass 49 "likelyadjust"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b8:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b5:b2:-:b8:14:17,b8:b2:-:-:20:23
cache loopnest 10 0 - -
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
dcllen 4
end
pass 50 "layout"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b8:b2,b5:b2,b3:b1
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b8:b2:-:-:20:23,b5:b2:-:b8:14:17,b3:b1:-:b2:5:8
cache loopnest 10 0 - -
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
fstate laidout
dcllen 4
end
pass 51 "schedule"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b8:b2,b5:b2,b3:b1
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b8:b2:-:-:20:23,b5:b2:-:b8:14:17,b3:b1:-:b2:5:8
cache loopnest 10 0 - -
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
fstate scheduled,laidout
dcllen 4
end
pass 52 "late nilcheck"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b8:b2,b5:b2,b3:b1
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b8:b2:-:-:20:23,b5:b2:-:b8:14:17,b3:b1:-:b2:5:8
cache loopnest 10 0 - -
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
fstate scheduled,laidout
dcllen 4
end
pass 53 "flagalloc"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v46,v25,v32,v33,v36,v15,v43,v21,v44,v11,v39,v45,v47,v7,v14,v10,v31,v30,v24,v20,v22,v38,v40,v29,v28,v26,v12,v19,v18,v16,v6,v5,v4,v3,v2
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b8:b2,b5:b2,b3:b1
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b8:b2:-:-:20:23,b5:b2:-:b8:14:17,b3:b1:-:b2:5:8
cache loopnest 10 0 - -
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
fstate scheduled,laidout
dcllen 4
end
pass 54 "regalloc"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v2,v3,v4,v5,v6,v7,v10,v11,v12,v14,v15,v16,v18,v19,v20,v21,v22,v24,v25,v26,v28,v29,v30,v31,v32,v33,v36,v38,v39,v40,v43,v44,v45,v46,v47
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b8:b2,b5:b2,b3:b1
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b8:b2:-:-:20:23,b5:b2:-:b8:14:17,b3:b1:-:b2:5:8
cache loopnest 10 0 - -
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
fstate scheduled,laidout
regalloc 43 v8:R3,v9:R4,v17:F0,v27:F1,v41:R1,v42:R0
dcllen 4
end
pass 55 "loop rotate"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v2,v3,v4,v5,v6,v7,v10,v11,v12,v14,v15,v16,v18,v19,v20,v21,v22,v24,v25,v26,v28,v29,v30,v31,v32,v33,v36,v38,v39,v40,v43,v44,v45,v46,v47
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b8:b2,b5:b2,b3:b1
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b8:b2:-:-:20:23,b5:b2:-:b8:14:17,b3:b1:-:b2:5:8
cache loopnest 10 0 - -
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
fstate scheduled,laidout
regalloc 43 v8:R3,v9:R4,v17:F0,v27:F1,v41:R1,v42:R0
dcllen 4
end
pass 56 "trim"
f b1 t1 a1 49 9
b b1 ARM64UGT p3:145:65:0:0 1 0 - v34 b2:0,b3:0 -
v v8 ArgIntReg t4 3 a7 p3:145:65:0:0 4 -
v v41 ArgIntReg t4 1 a10 p3:145:65:2:0 4 -
v v9 ArgIntReg t4 4 a8 p3:145:65:0:0 4 -
v v42 ArgIntReg t24 0 a9 p3:145:65:2:0 4 -
v v1 InitMem t29 0 - p0:0:0:0:0 5 -
v v34 ARM64CMP t30 0 - p3:145:65:1:0 1 v41,v8
b b2 ARM64UGT p3:145:59:0:0 1 0 - v35 b8:0,b5:0 b1:0
v v17 ARM64FMOVDloadidx8 t3 0 - p3:145:65:0:0 1 v42,v8,v1
v v35 ARM64CMP t30 0 - p3:145:59:0:0 1 v41,v9
b b8 Ret p3:145:69:0:0 0 0 - v49 - b2:0
v v27 ARM64FMOVDloadidx8 t3 0 - p3:145:59:0:0 1 v42,v9,v1
v v37 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v8,v27,v1
v v48 ARM64FMOVDstoreidx8 t29 0 - p3:145:56:0:0 1 v42,v9,v17,v37
v v49 MakeResult t33 0 - p3:145:69:0:0 1 v48
b b5 Exit p3:145:59:0:0 0 0 - v23 - b2:1
v v23 ARM64LoweredPanicBoundsRR t29 0 - p3:145:59:0:0 1 v9,v41,v1
b b3 Exit p3:145:65:0:0 0 0 - v13 - b1:1
v v13 ARM64LoweredPanicBoundsRR t29 0 - p3:145:65:0:0 1 v8,v41,v1
names s3,s2,s4,s5
named s3 v9
named s2 v8
named s4 v42
named s5 v41
splits s1/0/t24=s4,s1/8/t4=s5,s1/16/t4=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a5/t4/0/-/0=s3
consts -
freev v2,v3,v4,v5,v6,v7,v10,v11,v12,v14,v15,v16,v18,v19,v20,v21,v22,v24,v25,v26,v28,v29,v30,v31,v32,v33,v36,v38,v39,v40,v43,v44,v45,v46,v47
freeb b6,b4,b9,b7
cache postorder b8,b5,b2,b3,b1
cache idom b1:-,b2:b1,b8:b2,b5:b2,b3:b1
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b8:b2:-:-:20:23,b5:b2:-:b8:14:17,b3:b1:-:b2:5:8
cache loopnest 10 0 - -
cache auxmap a3:1,a4:2,a5:3,-:4,a7:5,a8:6,a9:7,a10:8
cache linestarts 3:145:145
fstate scheduled,laidout
regalloc 43 v8:R3,v9:R4,v17:F0,v27:F1,v41:R1,v42:R0
dcllen 4
end
frontend
end
ptrcache t2,t3,t4,t7,t8,t9,t10,t12,t14,t16,t17,t18,t25
typelink t29=t33
typeorder t6,t10,t7,t11,t8,t12,t9,t13,t4,t15,t16,t26,t27,t14,t3,t5,t18,t19,t20,t21,t22,t23,t24,t25,t34,t1,t2,t17,t28,t29,t31,t30,t32,t33
eof
"#

/-- `std/std/sort/Float64Slice.Swap,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "sort"
func "Float64Slice.Swap" 1
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
type t1 24 8 8 1 01 "Float64Slice"
name n1 "x" PPARAM t1 1 "sort.x" 0 a3
type t2 8 8 0 0 - "int"
name n2 "i" PPARAM t2 1 "sort.i" 0 a4
name n3 "j" PPARAM t2 1 "sort.j" 0 a5
type t3 8 8 0 0 - "float64"
name n4 ".autotmp_3" PAUTO t3 3 "sort..autotmp_3" 0 -
in n1 0 used
in n2 24 used
in n3 32 used
in n4 0 used,autotmp
out n1 0 used
out n2 24 used
out n3 32 used
opt n4 0 autotmp
stack 0 0 8
end
genin
posbase p3 "sort/sort.go" 1 1 -1 2 "sort/sort.go" "sort/sort.go" 1 1
type t4 8 8 8 1 01 "*uint8"
sym y1 "sort.Float64Slice.Swap" 1
curfn p3:145:6:0:0 0 0
regargs 8192:0:t4,8193:8:t2,8194:16:t2,8195:24:t2,8196:32:t2
text y1 0 0 0 0 145 201080
end
prog0
sym y2 "sort.x" 0
sym y3 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y4 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y5 "sort.Float64Slice.Swap.arginfo1" 0
sym y6 "sort.Float64Slice.Swap.argliveinfo" 0
sym y7 "runtime.panicBounds" 1
type t5 8 8 8 1 01 "*float64"
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i40 0 0 p3:145:6:0:0
p 22 22 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/PARAM/0/0/y2/- 0 0 p3:145:6:2:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p3:145:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p3:145:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p3:145:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p3:145:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p3:145:6:2:0
p 6 6 0 0 0 - CMP 0 REG/8195/0/0/NONE/0/0/-/- 8193 - _ 0 0 p3:145:65:1:0
p 7 7 0 0 0 - BLS 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@18 0 0 p3:145:65:2:0
p 8 8 0 0 0 - FMOVD 0 MEM/8192/8803/0/NONE/0/0/-/- 0 - REG/8224/0/0/NONE/0/0/-/- 0 0 p3:145:65:2:0
p 9 9 0 0 0 - CMP 0 REG/8196/0/0/NONE/0/0/-/- 8193 - _ 0 0 p3:145:59:2:0
p 10 10 0 0 0 - BLS 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@15 0 0 p3:145:59:2:0
p 11 11 0 0 0 - FMOVD 0 MEM/8192/8804/0/NONE/0/0/-/- 0 - REG/8225/0/0/NONE/0/0/-/- 0 0 p3:145:59:2:0
p 12 12 0 0 0 - FMOVD 0 REG/8225/0/0/NONE/0/0/-/- 0 - MEM/8192/8803/0/NONE/0/0/-/- 0 0 p3:145:56:2:0
p 13 13 0 0 0 - FMOVD 0 REG/8224/0/0/NONE/0/0/-/- 0 - MEM/8192/8804/0/NONE/0/0/-/- 0 0 p3:145:56:2:0
p 14 14 0 0 0 - RET 0 _ 0 - _ 0 0 p3:145:69:0:0
p 15 15 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p3:145:59:2:0
p 16 16 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/4/-/- 0 - CONST/0/0/0/NONE/0/1503/-/- 0 0 p3:145:59:2:0
p 17 17 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p3:145:59:2:0
p 18 18 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/4/-/- 0 - CONST/0/0/0/NONE/0/1431/-/- 0 0 p3:145:65:2:0
p 19 19 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p3:145:65:2:0
p 20 20 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p3:145:65:0:0
p 21 21 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 145 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 8195 STP LDP
spill MEM/8383/0/0/NONE/0/40/-/- 8196 0 MOVD MOVD
funcaux y3 y4 - - y5 y6 -
needzero -
regargs -
text 0 0 - 0
symalign y3:4,y4:4,y5:1,y6:1
autot -
dbgentry 1
dbgslot 0 n3 t2 0
dbgslot 1 n2 t2 0
dbgslot 2 n1 t5 0
dbgslot 3 n1 t2 8
dbgslot 4 n1 t2 16
dbgvar 0 n3 0
dbgvar 1 n2 1
dbgvar 2 n1 2,3,4
dbgloc 0 1:-10000:-1:-30000:54
dbgloc 1 1:-10000:-1:-30000:53
dbgloc 2 1:-10000:-1:-30000:509308519308529308
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
sym y17 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i40 0 0 p3:145:6:0:0
p 23 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p3:145:6:0:0
p 24 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p3:145:6:0:0
p 25 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p3:145:6:0:0
p 26 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@35 0 0 p3:145:6:0:0
p 27 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p3:145:6:0:0
p 28 12 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p3:145:6:0:1
p 29 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p3:145:6:0:0
p 30 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p3:145:6:0:0
p 22 24 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/0/y2/- 0 0 p3:145:6:2:0
p 1 28 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p3:145:6:0:0
p 2 28 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p3:145:6:0:0
p 3 28 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p3:145:6:0:0
p 4 28 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y6/- 0 0 p3:145:6:0:0
p 5 28 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p3:145:6:2:0
p 6 28 0 0 92 - CMP 0 REG/8195/0/0/NONE/2/0/-/- 8193 - NONE/0/0/0/NONE/1/0/-/- 0 0 p3:145:65:1:0
p 7 32 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/18/-/@18 0 0 p3:145:65:2:0
p 8 36 0 0 163 - FMOVD 0 MEM/8192/8803/0/NONE/114/0/-/- 0 - REG/8224/0/0/NONE/5/0/-/- 0 0 p3:145:65:2:0
p 9 40 0 0 92 - CMP 0 REG/8196/0/0/NONE/2/0/-/- 8193 - NONE/0/0/0/NONE/1/0/-/- 0 0 p3:145:59:2:0
p 10 44 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/15/-/@15 0 0 p3:145:59:2:0
p 11 48 0 0 163 - FMOVD 0 MEM/8192/8804/0/NONE/114/0/-/- 0 - REG/8225/0/0/NONE/5/0/-/- 0 0 p3:145:59:2:0
p 12 52 0 0 150 - FMOVD 0 REG/8225/0/0/NONE/5/0/-/- 0 - MEM/8192/8803/0/NONE/114/0/-/- 0 0 p3:145:56:2:0
p 13 56 0 0 150 - FMOVD 0 REG/8224/0/0/NONE/5/0/-/- 0 - MEM/8192/8804/0/NONE/114/0/-/- 0 0 p3:145:56:2:0
p 14 60 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p3:145:69:0:0
p 31 64 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p3:145:69:0:0
p 32 68 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p3:145:69:0:0
p 15 72 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p3:145:59:2:0
p 16 72 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/4/-/- 0 - CONST/0/0/0/NONE/18/1503/-/- 0 0 p3:145:59:2:0
p 17 72 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y7/- 0 0 p3:145:59:2:0
p 18 76 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/4/-/- 0 - CONST/0/0/0/NONE/18/1431/-/- 0 0 p3:145:65:2:0
p 19 76 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y7/- 0 0 p3:145:65:2:0
p 20 80 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p3:145:65:0:0
p 33 84 -16 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p3:145:65:0:0
p 34 84 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p3:145:6:0:0
p 35 84 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p3:145:6:0:0
p 36 84 0 0 436 - STP 0 REGREG/8192/0/0/NONE/7/8193/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p3:145:6:0:0
p 37 88 0 0 436 - STP 0 REGREG/8194/0/0/NONE/7/8195/-/- 0 - MEM/8383/0/0/NONE/87/24/-/- 0 0 p3:145:6:0:0
p 38 92 0 0 308 - MOVD 0 REG/8196/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/40/-/- 0 0 p3:145:6:0:0
p 39 96 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p3:145:6:0:0
p 40 100 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y8/- 0 0 p3:145:6:0:0
p 41 104 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p3:145:6:0:0
p 42 104 0 0 245 - LDP 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REGREG/8192/0/0/NONE/7/8193/-/- 0 0 p3:145:6:0:0
p 43 108 0 0 245 - LDP 0 MEM/8383/0/0/NONE/87/24/-/- 0 - REGREG/8194/0/0/NONE/7/8195/-/- 0 0 p3:145:6:0:0
p 44 112 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/40/-/- 0 - REG/8196/0/0/NONE/2/0/-/- 0 0 p3:145:6:0:0
p 45 116 16 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@23 0 0 p3:145:6:0:0
fn y1 40 8 0 0 145 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 8195 STP LDP
spill MEM/8383/0/0/NONE/0/40/-/- 8196 0 MOVD MOVD
funcaux y3 y4 - - y5 y6 -
text 128 0 900b40f9ff6330eb69020054fe0f1ff8fd831ff8fd2300d1e00f00f93f0003eb69010054007863fc3f0004ebe9000054017864fc017823fc007824fcfd835ff8fe0741f8c0035fd600000094000000941f2003d5e08700a9e28f01a9e41700f9e3031eaa00000094e08740a9e28f41a9e41740f9e3ffff170000000000000000 3
reloc 72 4 R_CALLARM64 0 y7
reloc 76 4 R_CALLARM64 0 y7
reloc 100 4 R_CALLARM64 0 y8
pcln y14 y15 y16 y17 y9,y10,y11,y12,y13 y3,y4,_,_,_,y5,y6
usedfiles 2
data y3 Sxxx 0 4 8000 02000000010000000100 0
data y4 Sxxx 0 4 8000 0200000000000000 0
data y5 SDATA 13 1 8000 fe000808081008fd18082008ff 0
data y6 SDATA 2 1 8000 0000 0
data y9 SRODATA 11 1 28000 0001010202120105020600 0
data y10 SRODATA 7 1 28000 00120403030b00 0
data y11 SRODATA 0 1 28000 - 0
data y12 SRODATA 5 1 28000 0007041900 0
data y13 SRODATA 9 1 28000 0012c017018f010d00 0
data y14 SRODATA 11 1 28000 0204200d1f0120031f0b00 0
data y15 SRODATA 3 1 28000 062000 0
data y16 SRODATA 4 1 28000 a4022000 0
data y17 SRODATA 3 1 28000 002000 0
end
dwarf
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
sym y21 "go:info.sort.Float64Slice.Swap$abstract" 0
sym y22 "" 0
sym y23 "go:info.sort.Float64Slice" 0
sym y24 "go:info.int" 0
dwfn y18 y19 y20 y21 y22 "sort.Float64Slice.Swap" 2:145 1 0 1 151
dwdcl n1,n2,n3
dwclosure 0 -
dwparents -
dwparams n1,n2,n3
dwprecursor y1 y21 n1,n2,n3
dwname n1 1 1 0 0 0 0 0 0 - - "sort.Float64Slice" 0 0 1 p3:145:7:0:0
dwname n2 1 1 0 0 0 0 24 0 - - "int" 0 0 1 p3:145:28:0:0
dwname n3 1 1 0 0 0 0 32 0 - - "int" 0 0 1 p3:145:31:0:0
dwname n4 1 0 1 0 0 0 0 0 - - "float64" 0 0 1 p3:145:56:0:0
var 0 0 "x" 5 1 0 0 0 8 y23 "sort/sort.go" 145 7 0 0 1 0 v2
var 1 0 "i" 5 1 0 0 0 32 y24 "sort/sort.go" 145 28 0 1 1 0 v1
var 2 0 "j" 5 1 0 0 0 40 y24 "sort/sort.go" 145 31 0 2 1 0 v0
scope 0 0 - 0,1,2
dieref y18 2 y21 0
dieref y18 4 y21 1
dieref y18 6 y21 2
dieoff y21 0:28,1:36,2:44
data y18 SDWARFFCN 39 0 0 060000000000008001019c29000000000000000029000000000000000029000000000000000000 8
reloc 1 4 R_DWARFSECREF 0 y21
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 12 4 R_DWARFSECREF 0 y21
reloc 16 4 R_DWARFSECREF 0 y19
reloc 21 4 R_DWARFSECREF 0 y21
reloc 25 4 R_DWARFSECREF 18 y19
reloc 30 4 R_DWARFSECREF 0 y21
reloc 34 4 R_DWARFSECREF 28 y19
data y19 SDWARFLOC 38 0 0 0100000400800109509308519308529308000100000400800101530001000004008001015400 3
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 19 2 R_DWTXTADDR_U2 0 y1
reloc 29 2 R_DWTXTADDR_U2 0 y1
data y20 SDWARFRANGE 0 0 0 - 0
data y22 SDWARFLINES 37 0 0 00090200000000000000000403038b01140a870687063706370608370687065f0230000101 1
reloc 3 8 R_ADDR 0 y1
data y21 SDWARFABSFCN 53 0 1 05736f72742e466c6f61743634536c6963652e53776170000191010122780000000000002269000000000000226a00000000000000 3
reloc 32 4 R_DWARFSECREF 0 y23
reloc 40 4 R_DWARFSECREF 0 y24
reloc 48 4 R_DWARFSECREF 0 y24
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `Float64Slice.Swap`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G45's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG45` gives (`b2`: `v17`'s `FMOVD (R0)(R3<<3), F0` at Prog 9, `v35`'s `CMP`,
then the `BLS`). -/
def tab : PcTab :=
  [(1, [6, 6, 6, 6, 6, 6, 8]), (2, [9, 10, 11]), (8, [12, 13, 14, 15, 15]), (5, [16, 19]),
    (3, [19, 21])]

/-- The class table `checkG45` gives. -/
def kt : KTab := (match checkG45 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 2).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- The machine address of `heap 1` (`GenG12.ι`). -/
def A : BitVec 64 := 0x20000000000

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `A` and the PC table of `checkG45`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The bits of `1.5`. -/
def bits : BitVec 64 := 0x3ff8000000000000

/-- The slice's array `x`: the start of the heap object `heap 1`. -/
def pB : Ptr := ⟨.heap 1, 0⟩

/-- The address `v17` loads from: `x + 1 · 8`. -/
def pQ : Ptr := ⟨.heap 1, 8⟩

/-- The bytes of `heap 1`: `x[0] = 0` and `x[1] = 1.5` (little-endian `bits` at offset 8). -/
def byteF (i : Nat) : BitVec 8 := if i = 14 then 0xf8 else if i = 15 then 0x3f else 0

/-- The Phase 1 memory before `v17`: `heap 1` a block of 16 bytes `byteF`. -/
def mem1 : Mem :=
  { blocks := #[(.heap 1, { data := Array.ofFn (n := 16) fun i => .b (byteF i.val) })],
    nextHeap := 2 }

/-- The machine memory before `v17`: the bytes of `heap 1` at `A`, 0 elsewhere. -/
def M1 : Memory := fun y => if (y - A).toNat < 16 then byteF (y - A).toNat else 0

/-- The `runLoc` state before `v17`: the array `x` (`pB`, `v42`) in `R0`, the index `i = 1`
(`v8`) in `R3`, every other register `poison`, the memory `mem1`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 0 then .ptr pB else if i.val = 3 then .i64 1 else .poison,
    flags := .poison, slots := [], mem := .mem mem1 }

/-- The machine before `v17`: `X0` the address `A` of `x`, `X3` 1, the V registers 0, the
activation's `g` and `FP`, the PC of `v17`, the memory `M1`. -/
def m0 : MState :=
  { x := fun k => if k = 0 then A else if k = 3 then 1 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 2 0, mem := M1 }

/-- The value is the 64-bit `bits`. -/
def isBitsV : Val → Bool
  | .int .w64 x => x == bits
  | _ => false

theorem isBitsV_spec {x : Val} (h : isBitsV x = true) : x = .int .w64 bits := by
  unfold isBitsV at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- The register holds the 64-bit `bits`. -/
def isBits : Option Val → Bool
  | some x => isBitsV x
  | none => false

theorem isBits_spec {o : Option Val} (h : isBits o = true) : o = some (.int .w64 bits) := by
  unfold isBits at h
  split at h
  · rw [isBitsV_spec h]
  · cases h

/-- `v17`'s address in `s0`: the arguments read as words whose `idxSum` at scale 8 addresses
`pQ`. -/
def addrIsQ (s : LocState) : Bool :=
  GenG1.okThen (s.read lc 42) fun x => GenG1.okThen (s.read lc 8) fun y =>
    Arm64.addr (idxSum (2 ^ 3) x y) 0 == some pQ

theorem addrIsQ_spec {s : LocState} (h : addrIsQ s = true) :
    ∃ x y, s.read lc 42 = .ok x ∧ s.read lc 8 = .ok y ∧
      Arm64.addr (idxSum (2 ^ 3) x y) 0 = some pQ := by
  obtain ⟨x, hx, h1⟩ := GenG1.okThen_spec h
  obtain ⟨y, hy, h2⟩ := GenG1.okThen_spec h1
  exact ⟨x, y, hx, hy, by simpa using h2⟩

/-- What compiled evaluation checks on `Float64Slice.Swap`: it holds an arm64 op; `checkG45`
accepts it with `tab` and `kt` and `checkG44` does not; it accesses no frame variable and has no
home slot; `b2` holds `v17` (`FMOVDloadidx8 v42 v8`, of type `float64`, in `F0`) at index 0, where
`R0` and `R3` have class 64 and G35's table is empty; in `s0` its address is `pQ`, where `mem1`
has 8 readable bytes, read at its shape as `bits`; `stepLoc` runs `v17` from `s0` to
`F0 = bits`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG45 lc0 ps bs g).toOption == some (tab, kt) && (checkG44 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 2 && (lc.ctx.f.block? 2).isSome &&
    (lc.ctx.f.value? 17).isSome && blk.values[0]? == some 17 &&
    (val 17).op == .ARM64FMOVDloadidx8 && (val 17).args[0]? == some 42 &&
    (val 17).args[1]? == some 8 &&
    (kAt lc kt 2 blk 0).get 0 == some 64 && (kAt lc kt 2 blk 0).get 3 == some 64 &&
    uL35 lc (uIn35 lc 2) blk 0 == [] &&
    addrIsQ s0 && (mem1.read pQ 8).isSome &&
    isBitsV ((Arm64.loadN (lc.ty (val 17).id) 8 false mem1 pQ).retypeL (lc.ty (val 17).id)) &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 17)) (fun s1 => isBits s1.regs[31]?)

theorem g45_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG45 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG44 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      2 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 2 = some blk ∧
      lc.ctx.f.value? 17 = some (val 17) ∧ blk.values[0]? = some 17 ∧
      (val 17).op = .ARM64FMOVDloadidx8 ∧ (val 17).args[0]? = some 42 ∧
      (val 17).args[1]? = some 8 ∧
      (kAt lc kt 2 blk 0).get 0 = some 64 ∧ (kAt lc kt 2 blk 0).get 3 = some 64 ∧
      uL35 lc (uIn35 lc 2) blk 0 = [] ∧ addrIsQ s0 = true ∧ (mem1.read pQ 8).isSome = true ∧
      isBitsV ((Arm64.loadN (lc.ty (val 17).id) 8 false mem1 pQ).retypeL (lc.ty (val 17).id)) =
        true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 17)) (fun s1 => isBits s1.regs[31]?) = true := by
  have hf := g45_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h44, hav, hsl, hm2, hbs, hvs, hi0, hop, ha0, ha1, hk0, hk3, hu0, hq, hrd, hbv,
    hrun⟩ := hf
  refine ⟨hl, ?_, h44, hav, hsl, hm2, ?_, ?_, hi0, hop, ha0, ha1, hk0, hk3, hu0, hq, hrd, hbv,
    hrun⟩
  · revert hres; cases checkG45 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g45Env (hc : checkG45 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
    (hav : (accessedVars lc).isEmpty = true) (hsl : (homeSlots lc).isEmpty = true) :
    G28Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        env := {
          lcEq := rfl
          link := rfl
          pcOf := rfl
          retOut := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
              checkG45L_spec hl (checkG45_spec hc).2
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
              checkG45L_spec hl (checkG45_spec hc).2
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
  memeqs := fun h => by cases h

/-! ## The memory -/

theorem mem1_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ mem1.blocks) :
    b = .heap 1 ∧ al = { data := Array.ofFn (n := 16) fun i => .b (byteF i.val) } := by
  simpa [mem1] using h

/-- `mem1` injected into `M1` by `GenG12.ι`: `heap 1`'s bytes at `A`. -/
theorem memInj1 : MemInj GenG12.ι mem1 M1 where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    exact ⟨A, rfl, fun _ => by decide, by simp [A]⟩
  inj := by
    intro b al b' al' a a' h h' hne
    obtain ⟨rfl, -⟩ := mem1_blocks h
    obtain ⟨rfl, -⟩ := mem1_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    have ha' : a = A := by simp [GenG12.ι] at ha; exact ha.symm
    subst ha'
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    simp only [Array.size_ofFn] at hi
    have hd : (A + BitVec.ofNat 64 i - A).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    simp [ByteRel, M1, hd, hi]

theorem keys1 : KeysNodup mem1 := by simp [KeysNodup, mem1]

theorem sep1 : SepFrom GenG12.ι (StkAt E) mem1 := by
  intro b al a h ha y hy
  obtain ⟨rfl, rfl⟩ := mem1_blocks h
  have ha' : a = A := by simp [GenG12.ι] at ha; exact ha.symm
  subst ha'
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    have hA : A.toNat = 0x20000000000 := rfl
    rw [hsp] at h2
    simp only [hA, Array.size_ofFn]
    omega
  · cases hk

/-! ## `v17`: `FMOVD (R0)(R3<<3), F0` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .ptr pB) ∨ (r = 3 ∧ x = .i64 1) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · split at h
      · rename_i _ h3; exact Or.inr (Or.inl ⟨h3, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatch0 : LocMatch E s0 2 0 m0 where
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
  mem := ⟨mem1, rfl, memInj1⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, M1, E, A]; decide,
    by simp only [MState.word, readMem, m0, M1, E, A]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g45Inv0 (h0 : (kAt lc kt 2 blk 0).get 0 = some 64)
    (h3 : (kAt lc kt 2 blk 0).get 3 = some 64) :
    G3Inv E lc (kAt lc kt 2 blk 0) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem1, rfl, keys1, sep1⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · rw [h3] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of G44 on `v17`, `FMOVDloadidx8`: none of them applies. -/
theorem pre44 (hop : (val 17).op = .ARM64FMOVDloadidx8) : G44Pre lc s0 (val 17) := by
  have hne : ∀ o : Op, o ≠ .ARM64FMOVDloadidx8 → (val 17).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
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

/-- `v17` reads 8 valid bytes of `heap 1` at `pQ`, read at its shape as the bits of `1.5`. -/
theorem fidxPre0 (hop : (val 17).op = .ARM64FMOVDloadidx8) (ha0 : (val 17).args[0]? = some 42)
    (ha1 : (val 17).args[1]? = some 8) (hq : addrIsQ s0 = true)
    (hrd : (mem1.read pQ 8).isSome = true)
    (hbv : isBitsV ((Arm64.loadN (lc.ty (val 17).id) 8 false mem1 pQ).retypeL
      (lc.ty (val 17).id)) = true) : FIdxPre lc s0 (val 17) := by
  intro n sh hl a0 a1 x y h0 h1 hx hy
  rw [hop] at hl
  simp only [fLoadIdxOp?, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, rfl⟩ := hl
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
  refine ⟨pQ, mem1, bs, hp, rfl, hbs, fun q hq' => ?_⟩
  rw [isBitsV_spec hbv] at hq'
  cases hq'

/-- **G45 on `sort.Float64Slice.Swap`**: `b2` loads `x[i]` (`v17`, `FMOVDloadidx8 v42 v8`, of type
`float64`, in `F0`) with the register-index `FMOVD (R0)(R3<<3), F0`, which `checkG44` rejects and
`checkG45` accepts. From `s0`, with the array `x` (`heap 1`) in `R0`, `i = 1` in `R3` and `x[1] =
1.5`, `stepLoc` runs `v17` to `F0 = 0x3ff8000000000000`, and `g45_value` relates it to a machine
state after `v17`'s code whose `V0` holds those bits in its low 64, under an activation extending
`E` that is again a `G28Env`. -/
theorem genG45_witness :
    (checkG44 lc0 ps bs g).toOption = none ∧ m0.x 3 = 1 ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 17) = .ok s1 ∧
        s1.regs[31]? = some (.int .w64 bits) ∧
        E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 2 1 m1 ∧ (m1.v 0).setWidth 64 = bits := by
  obtain ⟨hl, hc, h44, hav, hsl, hm2, hb, hv17, hi0, hop, ha0, ha1, hk0, hk3, hu0, hq, hrd, hbv,
    hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr1 := isBits_spec hr
  have hE := g45Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64FMOVDloadidx8 → (val 17).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g45_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hm0 : 2 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm2
  have hb0 : lc0.ctx.f.block? 2 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 17 = some (val 17) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv17
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g45_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi0 hv0 (by rw [hop]; rfl) locMatch0 (g45Inv0 hk0 hk3)
    (by change UOKL m0 (uL35 lc (uIn35 lc 2) blk 0); rw [hu0]; intro e he; cases he)
    ⟨pre44 hop, fidxPre0 hop ha0 ha1 hq hrd hbv⟩
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  refine ⟨h44, rfl, s1, E1, m1, hs1, hr1, hx1, hE1, hp1, hm1', ?_⟩
  exact (hm1'.regs 31 _ hr1).2 0 (by simp [objV?])

end GoFV.Proof.Witness.GenG45
