import GoFV.Gen.Check55
import GoFV.Proof.Gen.G57a
import GoFV.Proof.Witness.GenG2

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG57a

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `examples/structs/main/grow,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "grow" 1 0 0
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
type t5 INT32 4 4 0 comparable,named "int32" "int32"
type t4 STRUCT 8 4 0 comparable,named "point" "main.point" 2
field 0 "x" t5 0 0
field 1 "y" t5 4 0
type t6 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t3 STRUCT 32 8 24 hasptr,comparable,named "rect" "main.rect" 3
field 0 "min" t4 0 0
field 1 "max" t4 8 0
field 2 "name" t6 16 0
type t2 PTR 8 8 8 hasptr,direct,comparable "*rect" "*main.rect" t3
type t1 FUNC 8 8 8 hasptr,direct "func(*rect, int32) rect" "func(*main.rect, int32) main.rect" 0 2 1
field 0 "r" t2 ? 0
field 1 "d" t5 ? 0
field 2 "" t3 ? 0
aux a2 sym "main.grow" "main.grow" 1 - 0 - - - - 0
posbase p2 "./main.go" 1 1 -1
aux a3 name "r" "r" PPARAM t2 0 1 used p2:19:11:0:0
aux a4 name "d" "d" PPARAM t5 8 1 used p2:19:20:0:0
aux a5 name "~r0" "~r0" PPARAMOUT t3 0 1 - p2:19:29:0:0
aux a1 call "AuxCall{main.grow}" a2 1 2 1 8 16 2 6
abiparam in 0 t2 a3 0 0
abiparam in 1 t5 a4 1 8
abiparam out 0 t3 a5 0,1,2,3,4,5 -1
type t7 BOOL 1 1 0 comparable,named "bool" "bool"
type t8 INT8 1 1 0 comparable,named "int8" "int8"
type t9 INT16 2 2 0 comparable,named "int16" "int16"
type t10 INT64 8 8 0 comparable,named "int64" "int64"
type t11 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t12 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t13 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t14 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t15 INT 8 8 0 comparable,named "int" "int"
type t16 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t17 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t18 UINT 8 8 0 comparable,named "uint" "uint"
type t19 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t11
type t21 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t5
type t22 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t13
type t23 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t15
type t24 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t19
type t25 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t16
type t26 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t17
type t27 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t20
type t28 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t29 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t30 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t31 SSA ? ? ? - "mem" ""
type t32 SSA ? ? ? - "flags" ""
type t33 SSA ? ? ? - "void" ""
type t34 SSA 16 8 ? - "int128" ""
type t35 RESULTS ? ? ? - "mem" "" 1 t31
type t36 PTR 8 8 8 hasptr,direct,comparable "**rect" "**main.rect" t2
aux a6 str "" "" "go:string.\"\""
type t37 PTR 8 8 8 hasptr,direct,comparable "*point" "*main.point" t4
aux a7 type "int32" t5
aux a8 type "point" t4
type t38 RESULTS ? ? ? - "rect,mem" "" 2 t3,t31
slot s1 a3 t2 0 - 0
slot s2 a4 t5 0 - 0
f b1 t1 a1 52 1
typs Bool=t7,Int8=t8,Int16=t9,Int32=t5,Int64=t10,UInt8=t11,UInt16=t12,UInt32=t13,UInt64=t14,Int=t15,Float32=t16,Float64=t17,UInt=t18,Uintptr=t19,String=t6,BytePtr=t20,Int32Ptr=t21,UInt32Ptr=t22,IntPtr=t23,UintptrPtr=t24,Float32Ptr=t25,Float64Ptr=t26,BytePtrPtr=t27,Complex64=t28,Complex128=t29,UnsafePtr=t30,Mem=t31,Flags=t32,Void=t33,Int128=t34,ResultMem=t35
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v2 SP t19 0 - p0:0:0:0:0 3 -
v v3 SB t19 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t2 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v9 StructMake t3 0 - p0:0:0:0:0 0 v10,v12,v13
v v10 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v11 Const32 t5 0 - p0:0:0:0:0 6 -
v v12 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v13 ConstString t6 0 a6 p0:0:0:0:0 1 -
v v14 NilCheck t2 0 - p2:20:3:0:0 1 v7,v1
v v15 OffPtr t37 0 - p2:20:3:0:0 1 v14
v v16 OffPtr t21 0 - p2:20:7:0:0 1 v15
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 1 v7,v1
v v20 OffPtr t37 0 - p2:20:3:0:0 1 v19
v v21 OffPtr t21 0 - p2:20:7:0:0 1 v20
v v22 Store t31 0 a7 p2:20:10:0:0 4 v21,v18,v1
v v23 NilCheck t2 0 - p2:21:3:0:0 1 v7,v22
v v24 OffPtr t37 0 - p2:21:3:0:0 1 v23
v v25 OffPtr t21 4 - p2:21:7:0:0 1 v24
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 1 v7,v22
v v29 OffPtr t37 0 - p2:21:3:0:0 1 v28
v v30 OffPtr t21 4 - p2:21:7:0:0 1 v29
v v31 Store t31 0 a7 p2:21:10:0:0 6 v30,v27,v22
v v32 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v33 NilCheck t2 0 - p2:22:17:0:0 1 v7,v31
v v34 OffPtr t37 8 - p2:22:17:0:0 1 v33
v v35 OffPtr t21 0 - p2:22:21:0:0 1 v34
v v36 Load t5 0 - p2:22:21:0:0 1 v35,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v38 StructMake t4 0 - p2:22:24:0:0 1 v37,v39
v v39 StructSelect t5 1 - p2:22:24:0:0 1 v32
v v40 NilCheck t2 0 - p2:22:30:0:0 1 v7,v31
v v41 OffPtr t37 8 - p2:22:30:0:0 1 v40
v v42 OffPtr t21 4 - p2:22:34:0:0 1 v41
v v43 Load t5 0 - p2:22:34:0:0 1 v42,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v45 StructMake t4 0 - p2:22:37:0:0 1 v46,v44
v v46 StructSelect t5 0 - p2:22:37:0:0 1 v38
v v47 NilCheck t2 0 - p2:22:3:0:0 1 v7,v31
v v48 OffPtr t37 8 - p2:22:3:0:0 1 v47
v v49 Store t31 0 a8 p2:22:8:0:0 3 v48,v45,v31
v v50 NilCheck t2 0 - p2:23:9:0:0 1 v7,v49
v v51 Load t3 0 - p2:23:9:0:0 1 v50,v49
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v49
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts 0=v11,4455667788=v13
freev -
freeb -
dcllen 4
end
pass 1 "number lines"
f b1 t1 a1 52 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v2 SP t19 0 - p0:0:0:0:0 3 -
v v3 SB t19 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t2 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v9 StructMake t3 0 - p0:0:0:0:0 0 v10,v12,v13
v v10 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v11 Const32 t5 0 - p0:0:0:0:0 6 -
v v12 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v13 ConstString t6 0 a6 p0:0:0:0:0 1 -
v v14 NilCheck t2 0 - p2:20:3:1:0 1 v7,v1
v v15 OffPtr t37 0 - p2:20:3:0:0 1 v14
v v16 OffPtr t21 0 - p2:20:7:0:0 1 v15
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 1 v7,v1
v v20 OffPtr t37 0 - p2:20:3:0:0 1 v19
v v21 OffPtr t21 0 - p2:20:7:0:0 1 v20
v v22 Store t31 0 a7 p2:20:10:0:0 4 v21,v18,v1
v v23 NilCheck t2 0 - p2:21:3:1:0 1 v7,v22
v v24 OffPtr t37 0 - p2:21:3:0:0 1 v23
v v25 OffPtr t21 4 - p2:21:7:0:0 1 v24
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 1 v7,v22
v v29 OffPtr t37 0 - p2:21:3:0:0 1 v28
v v30 OffPtr t21 4 - p2:21:7:0:0 1 v29
v v31 Store t31 0 a7 p2:21:10:0:0 6 v30,v27,v22
v v32 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v33 NilCheck t2 0 - p2:22:17:1:0 1 v7,v31
v v34 OffPtr t37 8 - p2:22:17:0:0 1 v33
v v35 OffPtr t21 0 - p2:22:21:0:0 1 v34
v v36 Load t5 0 - p2:22:21:0:0 1 v35,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v38 StructMake t4 0 - p2:22:24:0:0 1 v37,v39
v v39 StructSelect t5 1 - p2:22:24:0:0 1 v32
v v40 NilCheck t2 0 - p2:22:30:0:0 1 v7,v31
v v41 OffPtr t37 8 - p2:22:30:0:0 1 v40
v v42 OffPtr t21 4 - p2:22:34:0:0 1 v41
v v43 Load t5 0 - p2:22:34:0:0 1 v42,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v45 StructMake t4 0 - p2:22:37:0:0 1 v46,v44
v v46 StructSelect t5 0 - p2:22:37:0:0 1 v38
v v47 NilCheck t2 0 - p2:22:3:0:0 1 v7,v31
v v48 OffPtr t37 8 - p2:22:3:0:0 1 v47
v v49 Store t31 0 a8 p2:22:8:0:0 3 v48,v45,v31
v v50 NilCheck t2 0 - p2:23:9:1:0 1 v7,v49
v v51 Load t3 0 - p2:23:9:0:0 1 v50,v49
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v49
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts 0=v11,4455667788=v13
freev -
freeb -
cache postorder b1
cache linestarts 2:20:23
dcllen 4
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 52 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v2 SP t19 0 - p0:0:0:0:0 3 -
v v3 SB t19 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t2 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v9 StructMake t3 0 - p0:0:0:0:0 0 v10,v12,v13
v v10 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v11 Const32 t5 0 - p0:0:0:0:0 6 -
v v12 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v13 ConstString t6 0 a6 p0:0:0:0:0 1 -
v v14 NilCheck t2 0 - p2:20:3:1:0 1 v7,v1
v v15 OffPtr t37 0 - p2:20:3:0:0 1 v14
v v16 OffPtr t21 0 - p2:20:7:0:0 1 v15
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 1 v7,v1
v v20 OffPtr t37 0 - p2:20:3:0:0 1 v19
v v21 OffPtr t21 0 - p2:20:7:0:0 1 v20
v v22 Store t31 0 a7 p2:20:10:0:0 4 v21,v18,v1
v v23 NilCheck t2 0 - p2:21:3:1:0 1 v7,v22
v v24 OffPtr t37 0 - p2:21:3:0:0 1 v23
v v25 OffPtr t21 4 - p2:21:7:0:0 1 v24
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 1 v7,v22
v v29 OffPtr t37 0 - p2:21:3:0:0 1 v28
v v30 OffPtr t21 4 - p2:21:7:0:0 1 v29
v v31 Store t31 0 a7 p2:21:10:0:0 6 v30,v27,v22
v v32 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v33 NilCheck t2 0 - p2:22:17:1:0 1 v7,v31
v v34 OffPtr t37 8 - p2:22:17:0:0 1 v33
v v35 OffPtr t21 0 - p2:22:21:0:0 1 v34
v v36 Load t5 0 - p2:22:21:0:0 1 v35,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v38 StructMake t4 0 - p2:22:24:0:0 1 v37,v39
v v39 StructSelect t5 1 - p2:22:24:0:0 1 v32
v v40 NilCheck t2 0 - p2:22:30:0:0 1 v7,v31
v v41 OffPtr t37 8 - p2:22:30:0:0 1 v40
v v42 OffPtr t21 4 - p2:22:34:0:0 1 v41
v v43 Load t5 0 - p2:22:34:0:0 1 v42,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v45 StructMake t4 0 - p2:22:37:0:0 1 v46,v44
v v46 StructSelect t5 0 - p2:22:37:0:0 1 v38
v v47 NilCheck t2 0 - p2:22:3:0:0 1 v7,v31
v v48 OffPtr t37 8 - p2:22:3:0:0 1 v47
v v49 Store t31 0 a8 p2:22:8:0:0 3 v48,v45,v31
v v50 NilCheck t2 0 - p2:23:9:1:0 1 v7,v49
v v51 Load t3 0 - p2:23:9:0:0 1 v50,v49
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v49
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts 0=v11,4455667788=v13
freev -
freeb -
cache postorder b1
cache linestarts 2:20:23
dcllen 4
end
pass 3 "early deadcode"
f b1 t1 a1 52 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v11 Const32 t5 0 - p0:0:0:0:0 2 -
v v14 NilCheck t2 0 - p2:20:3:1:0 1 v7,v1
v v15 OffPtr t37 0 - p2:20:3:0:0 1 v14
v v16 OffPtr t21 0 - p2:20:7:0:0 1 v15
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 1 v7,v1
v v20 OffPtr t37 0 - p2:20:3:0:0 1 v19
v v21 OffPtr t21 0 - p2:20:7:0:0 1 v20
v v22 Store t31 0 a7 p2:20:10:0:0 4 v21,v18,v1
v v23 NilCheck t2 0 - p2:21:3:1:0 1 v7,v22
v v24 OffPtr t37 0 - p2:21:3:0:0 1 v23
v v25 OffPtr t21 4 - p2:21:7:0:0 1 v24
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 1 v7,v22
v v29 OffPtr t37 0 - p2:21:3:0:0 1 v28
v v30 OffPtr t21 4 - p2:21:7:0:0 1 v29
v v31 Store t31 0 a7 p2:21:10:0:0 6 v30,v27,v22
v v32 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v33 NilCheck t2 0 - p2:22:17:1:0 1 v7,v31
v v34 OffPtr t37 8 - p2:22:17:0:0 1 v33
v v35 OffPtr t21 0 - p2:22:21:0:0 1 v34
v v36 Load t5 0 - p2:22:21:0:0 1 v35,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v38 StructMake t4 0 - p2:22:24:0:0 1 v37,v39
v v39 StructSelect t5 1 - p2:22:24:0:0 1 v32
v v40 NilCheck t2 0 - p2:22:30:0:0 1 v7,v31
v v41 OffPtr t37 8 - p2:22:30:0:0 1 v40
v v42 OffPtr t21 4 - p2:22:34:0:0 1 v41
v v43 Load t5 0 - p2:22:34:0:0 1 v42,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v45 StructMake t4 0 - p2:22:37:0:0 1 v46,v44
v v46 StructSelect t5 0 - p2:22:37:0:0 1 v38
v v47 NilCheck t2 0 - p2:22:3:0:0 1 v7,v31
v v48 OffPtr t37 8 - p2:22:3:0:0 1 v47
v v49 Store t31 0 a8 p2:22:8:0:0 3 v48,v45,v31
v v50 NilCheck t2 0 - p2:23:9:1:0 1 v7,v49
v v51 Load t3 0 - p2:23:9:0:0 1 v50,v49
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v49
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts 0=v11
freev v13,v12,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:20:23
dcllen 4
end
pass 4 "short circuit"
f b1 t1 a1 52 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v11 Const32 t5 0 - p0:0:0:0:0 2 -
v v14 NilCheck t2 0 - p2:20:3:1:0 1 v7,v1
v v15 OffPtr t37 0 - p2:20:3:0:0 1 v14
v v16 OffPtr t21 0 - p2:20:7:0:0 1 v15
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 1 v7,v1
v v20 OffPtr t37 0 - p2:20:3:0:0 1 v19
v v21 OffPtr t21 0 - p2:20:7:0:0 1 v20
v v22 Store t31 0 a7 p2:20:10:0:0 4 v21,v18,v1
v v23 NilCheck t2 0 - p2:21:3:1:0 1 v7,v22
v v24 OffPtr t37 0 - p2:21:3:0:0 1 v23
v v25 OffPtr t21 4 - p2:21:7:0:0 1 v24
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 1 v7,v22
v v29 OffPtr t37 0 - p2:21:3:0:0 1 v28
v v30 OffPtr t21 4 - p2:21:7:0:0 1 v29
v v31 Store t31 0 a7 p2:21:10:0:0 6 v30,v27,v22
v v32 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v33 NilCheck t2 0 - p2:22:17:1:0 1 v7,v31
v v34 OffPtr t37 8 - p2:22:17:0:0 1 v33
v v35 OffPtr t21 0 - p2:22:21:0:0 1 v34
v v36 Load t5 0 - p2:22:21:0:0 1 v35,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v38 StructMake t4 0 - p2:22:24:0:0 1 v37,v39
v v39 StructSelect t5 1 - p2:22:24:0:0 1 v32
v v40 NilCheck t2 0 - p2:22:30:0:0 1 v7,v31
v v41 OffPtr t37 8 - p2:22:30:0:0 1 v40
v v42 OffPtr t21 4 - p2:22:34:0:0 1 v41
v v43 Load t5 0 - p2:22:34:0:0 1 v42,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v45 StructMake t4 0 - p2:22:37:0:0 1 v46,v44
v v46 StructSelect t5 0 - p2:22:37:0:0 1 v38
v v47 NilCheck t2 0 - p2:22:3:0:0 1 v7,v31
v v48 OffPtr t37 8 - p2:22:3:0:0 1 v47
v v49 Store t31 0 a8 p2:22:8:0:0 3 v48,v45,v31
v v50 NilCheck t2 0 - p2:23:9:1:0 1 v7,v49
v v51 Load t3 0 - p2:23:9:0:0 1 v50,v49
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v49
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts 0=v11
freev v13,v12,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:20:23
dcllen 4
end
pass 5 "decompose user"
f b1 t1 a1 52 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v11 Const32 t5 0 - p0:0:0:0:0 2 -
v v14 NilCheck t2 0 - p2:20:3:1:0 1 v7,v1
v v15 OffPtr t37 0 - p2:20:3:0:0 1 v14
v v16 OffPtr t21 0 - p2:20:7:0:0 1 v15
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 1 v7,v1
v v20 OffPtr t37 0 - p2:20:3:0:0 1 v19
v v21 OffPtr t21 0 - p2:20:7:0:0 1 v20
v v22 Store t31 0 a7 p2:20:10:0:0 4 v21,v18,v1
v v23 NilCheck t2 0 - p2:21:3:1:0 1 v7,v22
v v24 OffPtr t37 0 - p2:21:3:0:0 1 v23
v v25 OffPtr t21 4 - p2:21:7:0:0 1 v24
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 1 v7,v22
v v29 OffPtr t37 0 - p2:21:3:0:0 1 v28
v v30 OffPtr t21 4 - p2:21:7:0:0 1 v29
v v31 Store t31 0 a7 p2:21:10:0:0 6 v30,v27,v22
v v32 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v33 NilCheck t2 0 - p2:22:17:1:0 1 v7,v31
v v34 OffPtr t37 8 - p2:22:17:0:0 1 v33
v v35 OffPtr t21 0 - p2:22:21:0:0 1 v34
v v36 Load t5 0 - p2:22:21:0:0 1 v35,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v38 StructMake t4 0 - p2:22:24:0:0 1 v37,v39
v v39 StructSelect t5 1 - p2:22:24:0:0 1 v32
v v40 NilCheck t2 0 - p2:22:30:0:0 1 v7,v31
v v41 OffPtr t37 8 - p2:22:30:0:0 1 v40
v v42 OffPtr t21 4 - p2:22:34:0:0 1 v41
v v43 Load t5 0 - p2:22:34:0:0 1 v42,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v45 StructMake t4 0 - p2:22:37:0:0 1 v46,v44
v v46 StructSelect t5 0 - p2:22:37:0:0 1 v38
v v47 NilCheck t2 0 - p2:22:3:0:0 1 v7,v31
v v48 OffPtr t37 8 - p2:22:3:0:0 1 v47
v v49 Store t31 0 a8 p2:22:8:0:0 3 v48,v45,v31
v v50 NilCheck t2 0 - p2:23:9:1:0 1 v7,v49
v v51 Load t3 0 - p2:23:9:0:0 1 v50,v49
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v49
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts 0=v11
freev v13,v12,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:20:23
dcllen 4
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 52 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v11 Const32 t5 0 - p0:0:0:0:0 2 -
v v14 NilCheck t2 0 - p2:20:3:1:0 1 v7,v1
v v15 OffPtr t37 0 - p2:20:3:0:0 1 v14
v v16 OffPtr t21 0 - p2:20:7:0:0 1 v15
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 1 v7,v1
v v20 OffPtr t37 0 - p2:20:3:0:0 1 v19
v v21 OffPtr t21 0 - p2:20:7:0:0 1 v20
v v22 Store t31 0 a7 p2:20:10:0:0 4 v21,v18,v1
v v23 NilCheck t2 0 - p2:21:3:1:0 1 v7,v22
v v24 OffPtr t37 0 - p2:21:3:0:0 1 v23
v v25 OffPtr t21 4 - p2:21:7:0:0 1 v24
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 1 v7,v22
v v29 OffPtr t37 0 - p2:21:3:0:0 1 v28
v v30 OffPtr t21 4 - p2:21:7:0:0 1 v29
v v31 Store t31 0 a7 p2:21:10:0:0 6 v30,v27,v22
v v32 StructMake t4 0 - p0:0:0:0:0 1 v11,v11
v v33 NilCheck t2 0 - p2:22:17:1:0 1 v7,v31
v v34 OffPtr t37 8 - p2:22:17:0:0 1 v33
v v35 OffPtr t21 0 - p2:22:21:0:0 1 v34
v v36 Load t5 0 - p2:22:21:0:0 1 v35,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v38 StructMake t4 0 - p2:22:24:0:0 1 v37,v39
v v39 StructSelect t5 1 - p2:22:24:0:0 1 v32
v v40 NilCheck t2 0 - p2:22:30:0:0 1 v7,v31
v v41 OffPtr t37 8 - p2:22:30:0:0 1 v40
v v42 OffPtr t21 4 - p2:22:34:0:0 1 v41
v v43 Load t5 0 - p2:22:34:0:0 1 v42,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v45 StructMake t4 0 - p2:22:37:0:0 1 v46,v44
v v46 StructSelect t5 0 - p2:22:37:0:0 1 v38
v v47 NilCheck t2 0 - p2:22:3:0:0 1 v7,v31
v v48 OffPtr t37 8 - p2:22:3:0:0 1 v47
v v49 Store t31 0 a8 p2:22:8:0:0 3 v48,v45,v31
v v50 NilCheck t2 0 - p2:23:9:1:0 1 v7,v49
v v51 Load t3 0 - p2:23:9:0:0 1 v50,v49
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v49
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts 0=v11
freev v13,v12,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:20:23
dcllen 4
end
pass 7 "opt"
type t39 PTR 8 8 8 hasptr,direct,comparable "*string" "*string" t6
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v14 NilCheck t2 0 - p2:20:3:1:0 1 v7,v1
v v16 OffPtr t21 0 - p2:20:7:0:0 1 v14
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 1 v7,v1
v v21 OffPtr t21 0 - p2:20:7:0:0 1 v19
v v22 Store t31 0 a7 p2:20:10:0:0 4 v21,v18,v1
v v23 NilCheck t2 0 - p2:21:3:1:0 1 v7,v22
v v25 OffPtr t21 4 - p2:21:7:0:0 1 v23
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 1 v7,v22
v v30 OffPtr t21 4 - p2:21:7:0:0 1 v28
v v31 Store t31 0 a7 p2:21:10:0:0 6 v30,v27,v22
v v33 NilCheck t2 0 - p2:22:17:1:0 1 v7,v31
v v35 OffPtr t21 8 - p2:22:21:0:0 1 v33
v v36 Load t5 0 - p2:22:21:0:0 1 v35,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v40 NilCheck t2 0 - p2:22:30:0:0 1 v7,v31
v v42 OffPtr t21 12 - p2:22:34:0:0 1 v40
v v43 Load t5 0 - p2:22:34:0:0 1 v42,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v47 NilCheck t2 0 - p2:22:3:0:0 2 v7,v31
v v50 NilCheck t2 0 - p2:23:9:1:0 5 v7,v9
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
v v13 OffPtr t21 8 - p2:22:8:0:0 1 v47
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v10 OffPtr t21 12 - p2:22:8:0:0 1 v47
v v9 Store t31 0 a7 p2:22:8:0:0 7 v10,v44,v12
v v5 StructMake t4 0 - p2:23:9:0:0 1 v55,v57
v v3 StructMake t4 0 - p2:23:9:0:0 1 v59,v61
v v2 OffPtr t39 16 - p2:23:9:0:0 1 v50
v v53 Load t6 0 - p2:23:9:0:0 1 v2,v9
v v54 OffPtr t21 0 - p2:23:9:0:0 1 v50
v v55 Load t5 0 - p2:23:9:0:0 1 v54,v9
v v56 OffPtr t21 4 - p2:23:9:0:0 1 v50
v v57 Load t5 0 - p2:23:9:0:0 1 v56,v9
v v58 OffPtr t21 8 - p2:23:9:0:0 1 v50
v v59 Load t5 0 - p2:23:9:0:0 1 v58,v9
v v60 OffPtr t21 12 - p2:23:9:0:0 1 v50
v v61 Load t5 0 - p2:23:9:0:0 1 v60,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache linestarts 2:20:23
dcllen 4
end
pass 8 "zero arg cse"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v14 NilCheck t2 0 - p2:20:3:1:0 1 v7,v1
v v16 OffPtr t21 0 - p2:20:7:0:0 1 v14
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 1 v7,v1
v v21 OffPtr t21 0 - p2:20:7:0:0 1 v19
v v22 Store t31 0 a7 p2:20:10:0:0 4 v21,v18,v1
v v23 NilCheck t2 0 - p2:21:3:1:0 1 v7,v22
v v25 OffPtr t21 4 - p2:21:7:0:0 1 v23
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 1 v7,v22
v v30 OffPtr t21 4 - p2:21:7:0:0 1 v28
v v31 Store t31 0 a7 p2:21:10:0:0 6 v30,v27,v22
v v33 NilCheck t2 0 - p2:22:17:1:0 1 v7,v31
v v35 OffPtr t21 8 - p2:22:21:0:0 1 v33
v v36 Load t5 0 - p2:22:21:0:0 1 v35,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v40 NilCheck t2 0 - p2:22:30:0:0 1 v7,v31
v v42 OffPtr t21 12 - p2:22:34:0:0 1 v40
v v43 Load t5 0 - p2:22:34:0:0 1 v42,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v47 NilCheck t2 0 - p2:22:3:0:0 2 v7,v31
v v50 NilCheck t2 0 - p2:23:9:1:0 5 v7,v9
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
v v13 OffPtr t21 8 - p2:22:8:0:0 1 v47
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v10 OffPtr t21 12 - p2:22:8:0:0 1 v47
v v9 Store t31 0 a7 p2:22:8:0:0 7 v10,v44,v12
v v5 StructMake t4 0 - p2:23:9:0:0 1 v55,v57
v v3 StructMake t4 0 - p2:23:9:0:0 1 v59,v61
v v2 OffPtr t39 16 - p2:23:9:0:0 1 v50
v v53 Load t6 0 - p2:23:9:0:0 1 v2,v9
v v54 OffPtr t21 0 - p2:23:9:0:0 1 v50
v v55 Load t5 0 - p2:23:9:0:0 1 v54,v9
v v56 OffPtr t21 4 - p2:23:9:0:0 1 v50
v v57 Load t5 0 - p2:23:9:0:0 1 v56,v9
v v58 OffPtr t21 8 - p2:23:9:0:0 1 v50
v v59 Load t5 0 - p2:23:9:0:0 1 v58,v9
v v60 OffPtr t21 12 - p2:23:9:0:0 1 v50
v v61 Load t5 0 - p2:23:9:0:0 1 v60,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache linestarts 2:20:23
dcllen 4
end
pass 9 "opt deadcode"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v14 NilCheck t2 0 - p2:20:3:1:0 1 v7,v1
v v16 OffPtr t21 0 - p2:20:7:0:0 1 v14
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 1 v7,v1
v v21 OffPtr t21 0 - p2:20:7:0:0 1 v19
v v22 Store t31 0 a7 p2:20:10:0:0 4 v21,v18,v1
v v23 NilCheck t2 0 - p2:21:3:1:0 1 v7,v22
v v25 OffPtr t21 4 - p2:21:7:0:0 1 v23
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 1 v7,v22
v v30 OffPtr t21 4 - p2:21:7:0:0 1 v28
v v31 Store t31 0 a7 p2:21:10:0:0 6 v30,v27,v22
v v33 NilCheck t2 0 - p2:22:17:1:0 1 v7,v31
v v35 OffPtr t21 8 - p2:22:21:0:0 1 v33
v v36 Load t5 0 - p2:22:21:0:0 1 v35,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v40 NilCheck t2 0 - p2:22:30:0:0 1 v7,v31
v v42 OffPtr t21 12 - p2:22:34:0:0 1 v40
v v43 Load t5 0 - p2:22:34:0:0 1 v42,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v47 NilCheck t2 0 - p2:22:3:0:0 2 v7,v31
v v50 NilCheck t2 0 - p2:23:9:1:0 5 v7,v9
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
v v13 OffPtr t21 8 - p2:22:8:0:0 1 v47
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v10 OffPtr t21 12 - p2:22:8:0:0 1 v47
v v9 Store t31 0 a7 p2:22:8:0:0 7 v10,v44,v12
v v5 StructMake t4 0 - p2:23:9:0:0 1 v55,v57
v v3 StructMake t4 0 - p2:23:9:0:0 1 v59,v61
v v2 OffPtr t39 16 - p2:23:9:0:0 1 v50
v v53 Load t6 0 - p2:23:9:0:0 1 v2,v9
v v54 OffPtr t21 0 - p2:23:9:0:0 1 v50
v v55 Load t5 0 - p2:23:9:0:0 1 v54,v9
v v56 OffPtr t21 4 - p2:23:9:0:0 1 v50
v v57 Load t5 0 - p2:23:9:0:0 1 v56,v9
v v58 OffPtr t21 8 - p2:23:9:0:0 1 v50
v v59 Load t5 0 - p2:23:9:0:0 1 v58,v9
v v60 OffPtr t21 12 - p2:23:9:0:0 1 v50
v v61 Load t5 0 - p2:23:9:0:0 1 v60,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache linestarts 2:20:23
dcllen 4
end
pass 10 "generic cse"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v14 NilCheck t2 0 - p2:20:3:1:0 13 v7,v1
v v16 OffPtr t21 0 - p2:20:7:0:0 3 v14
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 0 v7,v1
v v21 OffPtr t21 0 - p2:20:7:0:0 0 v14
v v22 Store t31 0 a7 p2:20:10:0:0 4 v16,v18,v1
v v23 NilCheck t2 0 - p2:21:3:1:0 0 v7,v22
v v25 OffPtr t21 4 - p2:21:7:0:0 3 v14
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 0 v7,v22
v v30 OffPtr t21 4 - p2:21:7:0:0 0 v14
v v31 Store t31 0 a7 p2:21:10:0:0 6 v25,v27,v22
v v33 NilCheck t2 0 - p2:22:17:1:0 0 v7,v31
v v35 OffPtr t21 8 - p2:22:21:0:0 0 v14
v v36 Load t5 0 - p2:22:21:0:0 1 v13,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v40 NilCheck t2 0 - p2:22:30:0:0 0 v7,v31
v v42 OffPtr t21 12 - p2:22:34:0:0 0 v14
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v47 NilCheck t2 0 - p2:22:3:0:0 0 v7,v31
v v50 NilCheck t2 0 - p2:23:9:1:0 0 v7,v9
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
v v13 OffPtr t21 8 - p2:22:8:0:0 3 v14
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v10 OffPtr t21 12 - p2:22:8:0:0 3 v14
v v9 Store t31 0 a7 p2:22:8:0:0 7 v10,v44,v12
v v5 StructMake t4 0 - p2:23:9:0:0 1 v55,v57
v v3 StructMake t4 0 - p2:23:9:0:0 1 v59,v61
v v2 OffPtr t39 16 - p2:23:9:0:0 1 v14
v v53 Load t6 0 - p2:23:9:0:0 1 v2,v9
v v54 OffPtr t21 0 - p2:23:9:0:0 0 v14
v v55 Load t5 0 - p2:23:9:0:0 1 v16,v9
v v56 OffPtr t21 4 - p2:23:9:0:0 0 v14
v v57 Load t5 0 - p2:23:9:0:0 1 v25,v9
v v58 OffPtr t21 8 - p2:23:9:0:0 0 v14
v v59 Load t5 0 - p2:23:9:0:0 1 v13,v9
v v60 OffPtr t21 12 - p2:23:9:0:0 0 v14
v v61 Load t5 0 - p2:23:9:0:0 1 v10,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 11 "phiopt"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v14 NilCheck t2 0 - p2:20:3:1:0 13 v7,v1
v v16 OffPtr t21 0 - p2:20:7:0:0 3 v14
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 0 v7,v1
v v21 OffPtr t21 0 - p2:20:7:0:0 0 v14
v v22 Store t31 0 a7 p2:20:10:0:0 4 v16,v18,v1
v v23 NilCheck t2 0 - p2:21:3:1:0 0 v7,v22
v v25 OffPtr t21 4 - p2:21:7:0:0 3 v14
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 0 v7,v22
v v30 OffPtr t21 4 - p2:21:7:0:0 0 v14
v v31 Store t31 0 a7 p2:21:10:0:0 6 v25,v27,v22
v v33 NilCheck t2 0 - p2:22:17:1:0 0 v7,v31
v v35 OffPtr t21 8 - p2:22:21:0:0 0 v14
v v36 Load t5 0 - p2:22:21:0:0 1 v13,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v40 NilCheck t2 0 - p2:22:30:0:0 0 v7,v31
v v42 OffPtr t21 12 - p2:22:34:0:0 0 v14
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v47 NilCheck t2 0 - p2:22:3:0:0 0 v7,v31
v v50 NilCheck t2 0 - p2:23:9:1:0 0 v7,v9
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
v v13 OffPtr t21 8 - p2:22:8:0:0 3 v14
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v10 OffPtr t21 12 - p2:22:8:0:0 3 v14
v v9 Store t31 0 a7 p2:22:8:0:0 7 v10,v44,v12
v v5 StructMake t4 0 - p2:23:9:0:0 1 v55,v57
v v3 StructMake t4 0 - p2:23:9:0:0 1 v59,v61
v v2 OffPtr t39 16 - p2:23:9:0:0 1 v14
v v53 Load t6 0 - p2:23:9:0:0 1 v2,v9
v v54 OffPtr t21 0 - p2:23:9:0:0 0 v14
v v55 Load t5 0 - p2:23:9:0:0 1 v16,v9
v v56 OffPtr t21 4 - p2:23:9:0:0 0 v14
v v57 Load t5 0 - p2:23:9:0:0 1 v25,v9
v v58 OffPtr t21 8 - p2:23:9:0:0 0 v14
v v59 Load t5 0 - p2:23:9:0:0 1 v13,v9
v v60 OffPtr t21 12 - p2:23:9:0:0 0 v14
v v61 Load t5 0 - p2:23:9:0:0 1 v10,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 12 "gcse deadcode"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:19:6:2:0 8 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v14 NilCheck t2 0 - p2:20:3:1:0 5 v7,v1
v v16 OffPtr t21 0 - p2:20:7:0:0 3 v14
v v17 Load t5 0 - p2:20:7:0:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v19 NilCheck t2 0 - p2:20:3:0:0 0 v7,v1
v v22 Store t31 0 a7 p2:20:10:0:0 4 v16,v18,v1
v v23 NilCheck t2 0 - p2:21:3:1:0 0 v7,v22
v v25 OffPtr t21 4 - p2:21:7:0:0 3 v14
v v26 Load t5 0 - p2:21:7:0:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v28 NilCheck t2 0 - p2:21:3:0:0 0 v7,v22
v v31 Store t31 0 a7 p2:21:10:0:0 6 v25,v27,v22
v v33 NilCheck t2 0 - p2:22:17:1:0 0 v7,v31
v v36 Load t5 0 - p2:22:21:0:0 1 v13,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v40 NilCheck t2 0 - p2:22:30:0:0 0 v7,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v47 NilCheck t2 0 - p2:22:3:0:0 0 v7,v31
v v50 NilCheck t2 0 - p2:23:9:1:0 0 v7,v9
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
v v13 OffPtr t21 8 - p2:22:8:0:0 3 v14
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v10 OffPtr t21 12 - p2:22:8:0:0 3 v14
v v9 Store t31 0 a7 p2:22:8:0:0 7 v10,v44,v12
v v5 StructMake t4 0 - p2:23:9:0:0 1 v55,v57
v v3 StructMake t4 0 - p2:23:9:0:0 1 v59,v61
v v2 OffPtr t39 16 - p2:23:9:0:0 1 v14
v v53 Load t6 0 - p2:23:9:0:0 1 v2,v9
v v55 Load t5 0 - p2:23:9:0:0 1 v16,v9
v v57 Load t5 0 - p2:23:9:0:0 1 v25,v9
v v59 Load t5 0 - p2:23:9:0:0 1 v13,v9
v v61 Load t5 0 - p2:23:9:0:0 1 v10,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v60,v58,v56,v54,v42,v35,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 13 "nilcheckelim"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v7 Arg t2 0 a3 p2:19:6:2:0 1 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v19 NilCheck t2 0 - p2:20:3:0:0 7 v7,v1
v v14 Copy t2 0 - p2:20:3:1:0 5 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 3 v14
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v25 OffPtr t21 4 - p2:21:7:0:0 3 v14
v v13 OffPtr t21 8 - p2:22:8:0:0 3 v14
v v10 OffPtr t21 12 - p2:22:8:0:0 3 v14
v v2 OffPtr t39 16 - p2:23:9:0:0 1 v14
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v28 Copy t2 0 - p2:21:3:0:0 0 v19
v v23 Copy t2 0 - p2:21:3:1:0 0 v19
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v47 Copy t2 0 - p2:22:3:0:0 0 v19
v v33 Copy t2 0 - p2:22:17:1:0 0 v19
v v40 Copy t2 0 - p2:22:30:0:0 0 v19
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 6 v10,v44,v12
v v50 Copy t2 0 - p2:23:9:1:0 0 v19
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v5 StructMake t4 0 - p2:23:9:0:0 1 v55,v57
v v3 StructMake t4 0 - p2:23:9:0:0 1 v59,v61
v v53 Load t6 0 - p2:23:9:1:0 1 v2,v9
v v55 Load t5 0 - p2:23:9:0:0 1 v16,v9
v v57 Load t5 0 - p2:23:9:0:0 1 v25,v9
v v59 Load t5 0 - p2:23:9:0:0 1 v13,v9
v v61 Load t5 0 - p2:23:9:0:0 1 v10,v9
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v60,v58,v56,v54,v42,v35,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 14 "prove"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p2:19:6:2:0 1 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v19 NilCheck t2 0 - p2:20:3:0:0 7 v7,v1
v v14 Copy t2 0 - p2:20:3:1:0 5 v19
v v23 Copy t2 0 - p2:21:3:1:0 0 v19
v v28 Copy t2 0 - p2:21:3:0:0 0 v19
v v33 Copy t2 0 - p2:22:17:1:0 0 v19
v v40 Copy t2 0 - p2:22:30:0:0 0 v19
v v47 Copy t2 0 - p2:22:3:0:0 0 v19
v v50 Copy t2 0 - p2:23:9:1:0 0 v19
v v2 OffPtr t39 16 - p2:23:9:0:0 1 v14
v v10 OffPtr t21 12 - p2:22:8:0:0 3 v14
v v13 OffPtr t21 8 - p2:22:8:0:0 3 v14
v v16 OffPtr t21 0 - p2:20:7:0:0 3 v14
v v25 OffPtr t21 4 - p2:21:7:0:0 3 v14
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 6 v10,v44,v12
v v53 Load t6 0 - p2:23:9:1:0 1 v2,v9
v v55 Load t5 0 - p2:23:9:0:0 1 v16,v9
v v57 Load t5 0 - p2:23:9:0:0 1 v25,v9
v v59 Load t5 0 - p2:23:9:0:0 1 v13,v9
v v61 Load t5 0 - p2:23:9:0:0 1 v10,v9
v v3 StructMake t4 0 - p2:23:9:0:0 1 v59,v61
v v5 StructMake t4 0 - p2:23:9:0:0 1 v55,v57
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v60,v58,v56,v54,v42,v35,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 15 "divisible"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p2:19:6:2:0 1 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 5 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 3 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 3 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 3 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 3 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 6 v10,v44,v12
v v53 Load t6 0 - p2:23:9:1:0 1 v2,v9
v v55 Load t5 0 - p2:23:9:0:0 1 v16,v9
v v57 Load t5 0 - p2:23:9:0:0 1 v25,v9
v v59 Load t5 0 - p2:23:9:0:0 1 v13,v9
v v61 Load t5 0 - p2:23:9:0:0 1 v10,v9
v v3 StructMake t4 0 - p2:23:9:0:0 1 v59,v61
v v5 StructMake t4 0 - p2:23:9:0:0 1 v55,v57
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v50,v47,v40,v33,v28,v23,v14,v60,v58,v56,v54,v42,v35,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 16 "divmod"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p2:19:6:2:0 1 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 5 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 3 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 3 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 3 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 3 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 1 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 1 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 1 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 1 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 6 v10,v44,v12
v v53 Load t6 0 - p2:23:9:1:0 1 v2,v9
v v55 Load t5 0 - p2:23:9:0:0 1 v16,v9
v v57 Load t5 0 - p2:23:9:0:0 1 v25,v9
v v59 Load t5 0 - p2:23:9:0:0 1 v13,v9
v v61 Load t5 0 - p2:23:9:0:0 1 v10,v9
v v3 StructMake t4 0 - p2:23:9:0:0 1 v59,v61
v v5 StructMake t4 0 - p2:23:9:0:0 1 v55,v57
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v50,v47,v40,v33,v28,v23,v14,v60,v58,v56,v54,v42,v35,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 17 "middle opt"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p2:19:6:2:0 1 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 5 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 2 v10,v44,v12
v v53 Load t6 0 - p2:23:9:1:0 1 v2,v9
v v3 StructMake t4 0 - p2:23:9:0:0 1 v37,v44
v v5 StructMake t4 0 - p2:23:9:0:0 1 v18,v27
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v61,v59,v57,v55,v50,v47,v40,v33,v28,v23,v14,v60,v58,v56,v54,v42,v35,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 18 "known bits"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p2:19:6:2:0 1 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 5 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 2 v10,v44,v12
v v53 Load t6 0 - p2:23:9:1:0 1 v2,v9
v v3 StructMake t4 0 - p2:23:9:0:0 1 v37,v44
v v5 StructMake t4 0 - p2:23:9:0:0 1 v18,v27
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v61,v59,v57,v55,v50,v47,v40,v33,v28,v23,v14,v60,v58,v56,v54,v42,v35,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 19 "early fuse"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p2:19:6:2:0 1 -
v v8 Arg t5 0 a4 p2:19:6:2:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 5 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 2 v10,v44,v12
v v53 Load t6 0 - p2:23:9:1:0 1 v2,v9
v v3 StructMake t4 0 - p2:23:9:0:0 1 v37,v44
v v5 StructMake t4 0 - p2:23:9:0:0 1 v18,v27
v v51 StructMake t3 0 - p2:23:9:0:0 1 v5,v3,v53
v v52 MakeResult t38 0 - p2:23:2:0:0 1 v51,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v61,v59,v57,v55,v50,v47,v40,v33,v28,v23,v14,v60,v58,v56,v54,v42,v35,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 20 "expand calls"
aux a9 nameoff "r+0" a3 0
aux a10 nameoff "d+0" a4 0
type t40 RESULTS ? ? ? - "int32,int32,int32,int32,*uint8,int,mem" "" 7 t5,t5,t5,t5,t20,t15,t31
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 5 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 3 v10,v44,v12
v v53 Load t6 0 - p2:23:9:1:0 1 v2,v9
v v3 StructMake t4 0 - p2:23:9:0:0 1 v37,v44
v v5 StructMake t4 0 - p2:23:9:0:0 1 v18,v27
v v51 StructMake t3 0 - p2:23:9:0:0 3 v5,v3,v53
v v52 MakeResult t40 0 - p2:23:2:0:0 1 v40,v33,v23,v14,v58,v56,v9
v v61 SB t19 0 - p0:0:0:0:0 0 -
v v59 SP t19 0 - p0:0:0:0:0 3 -
v v57 OffPtr t36 0 - p0:0:0:0:0 0 v59
v v55 OffPtr t21 0 - p0:0:0:0:0 0 v59
v v50 LocalAddr t2 0 a5 p2:23:2:0:0 0 v59,v9
v v47 StructSelect t4 0 - p2:23:2:0:0 2 v51
v v40 StructSelect t5 0 - p2:23:2:2:0 1 v47
v v33 StructSelect t5 1 - p2:23:2:2:0 1 v47
v v28 StructSelect t4 1 - p2:23:2:2:0 2 v51
v v23 StructSelect t5 0 - p2:23:2:2:0 1 v28
v v14 StructSelect t5 1 - p2:23:2:2:0 1 v28
v v60 StructSelect t6 2 - p2:23:2:2:0 2 v51
v v58 StringPtr t20 0 - p2:23:2:2:0 1 v60
v v56 StringLen t15 0 - p2:23:2:2:0 1 v60
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts 0=v57,v55
freev v54,v42,v35,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 21 "decompose builtin"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 5 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 2 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 3 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 3 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 3 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 3 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 4 v10,v44,v12
v v53 StringMake t6 0 - p2:23:9:2:0 1 v54,v42
v v3 StructMake t4 0 - p2:23:9:0:0 1 v37,v44
v v5 StructMake t4 0 - p2:23:9:0:0 1 v18,v27
v v51 StructMake t3 0 - p2:23:9:0:0 0 v5,v3,v53
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v61 SB t19 0 - p0:0:0:0:0 0 -
v v59 SP t19 0 - p0:0:0:0:0 3 -
v v57 OffPtr t36 0 - p0:0:0:0:0 0 v59
v v55 OffPtr t21 0 - p0:0:0:0:0 0 v59
v v50 LocalAddr t2 0 a5 p2:23:2:0:0 0 v59,v9
v v54 Load t20 0 - p2:23:9:1:0 2 v2,v9
v v42 Load t15 0 - p2:23:9:1:0 2 v35,v9
v v35 OffPtr t23 8 - p2:23:9:1:0 1 v2
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts 0=v57,v55
freev v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 22 "softfloat"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 5 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 2 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 3 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 3 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 3 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 3 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 4 v10,v44,v12
v v53 StringMake t6 0 - p2:23:9:2:0 1 v54,v42
v v3 StructMake t4 0 - p2:23:9:0:0 1 v37,v44
v v5 StructMake t4 0 - p2:23:9:0:0 1 v18,v27
v v51 StructMake t3 0 - p2:23:9:0:0 0 v5,v3,v53
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v61 SB t19 0 - p0:0:0:0:0 0 -
v v59 SP t19 0 - p0:0:0:0:0 3 -
v v57 OffPtr t36 0 - p0:0:0:0:0 0 v59
v v55 OffPtr t21 0 - p0:0:0:0:0 0 v59
v v50 LocalAddr t2 0 a5 p2:23:2:0:0 0 v59,v9
v v54 Load t20 0 - p2:23:9:1:0 2 v2,v9
v v42 Load t15 0 - p2:23:9:1:0 2 v35,v9
v v35 OffPtr t23 8 - p2:23:9:1:0 1 v2
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts 0=v57,v55
freev v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 23 "branchelim"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 5 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 2 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 3 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 3 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 3 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 3 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 4 v10,v44,v12
v v53 StringMake t6 0 - p2:23:9:2:0 1 v54,v42
v v3 StructMake t4 0 - p2:23:9:0:0 1 v37,v44
v v5 StructMake t4 0 - p2:23:9:0:0 1 v18,v27
v v51 StructMake t3 0 - p2:23:9:0:0 0 v5,v3,v53
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v61 SB t19 0 - p0:0:0:0:0 0 -
v v59 SP t19 0 - p0:0:0:0:0 3 -
v v57 OffPtr t36 0 - p0:0:0:0:0 0 v59
v v55 OffPtr t21 0 - p0:0:0:0:0 0 v59
v v50 LocalAddr t2 0 a5 p2:23:2:0:0 0 v59,v9
v v54 Load t20 0 - p2:23:9:1:0 2 v2,v9
v v42 Load t15 0 - p2:23:9:1:0 2 v35,v9
v v35 OffPtr t23 8 - p2:23:9:1:0 1 v2
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts 0=v57,v55
freev v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 24 "late opt"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 6 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 3 v10,v44,v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 Load t20 0 - p2:23:9:1:0 1 v2,v9
v v42 Load t15 0 - p2:23:9:1:0 1 v35,v9
v v35 OffPtr t23 24 - p2:23:9:1:0 1 v19
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 25 "dead auto elim"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 6 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 3 v10,v44,v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 Load t20 0 - p2:23:9:1:0 1 v2,v9
v v42 Load t15 0 - p2:23:9:1:0 1 v35,v9
v v35 OffPtr t23 24 - p2:23:9:1:0 1 v19
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 26 "sccp"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 6 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 3 v10,v44,v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 Load t20 0 - p2:23:9:1:0 1 v2,v9
v v42 Load t15 0 - p2:23:9:1:0 1 v35,v9
v v35 OffPtr t23 24 - p2:23:9:1:0 1 v19
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 27 "generic deadcode"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 6 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 3 v10,v44,v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 Load t20 0 - p2:23:9:1:0 1 v2,v9
v v42 Load t15 0 - p2:23:9:1:0 1 v35,v9
v v35 OffPtr t23 24 - p2:23:9:1:0 1 v19
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 28 "late fuse"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 6 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 3 v10,v44,v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 Load t20 0 - p2:23:9:1:0 1 v2,v9
v v42 Load t15 0 - p2:23:9:1:0 1 v35,v9
v v35 OffPtr t23 24 - p2:23:9:1:0 1 v19
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 29 "check bce"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 6 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 3 v10,v44,v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 Load t20 0 - p2:23:9:1:0 1 v2,v9
v v42 Load t15 0 - p2:23:9:1:0 1 v35,v9
v v35 OffPtr t23 24 - p2:23:9:1:0 1 v19
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 30 "dse"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 6 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 3 v10,v44,v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 Load t20 0 - p2:23:9:1:0 1 v2,v9
v v42 Load t15 0 - p2:23:9:1:0 1 v35,v9
v v35 OffPtr t23 24 - p2:23:9:1:0 1 v19
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 31 "memcombine"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 6 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 3 v10,v44,v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 Load t20 0 - p2:23:9:1:0 1 v2,v9
v v42 Load t15 0 - p2:23:9:1:0 1 v35,v9
v v35 OffPtr t23 24 - p2:23:9:1:0 1 v19
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 32 "writebarrier"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 NilCheck t2 0 - p2:20:3:1:0 6 v7,v1
v v2 OffPtr t39 16 - p2:23:9:1:0 1 v19
v v10 OffPtr t21 12 - p2:22:8:1:0 2 v19
v v13 OffPtr t21 8 - p2:22:8:0:0 2 v19
v v16 OffPtr t21 0 - p2:20:7:0:0 2 v19
v v25 OffPtr t21 4 - p2:21:7:1:0 2 v19
v v17 Load t5 0 - p2:20:7:1:0 1 v16,v1
v v18 Sub32 t5 0 - p2:20:10:0:0 2 v17,v8
v v22 Store t31 0 a7 p2:20:10:0:0 2 v16,v18,v1
v v26 Load t5 0 - p2:21:7:1:0 1 v25,v22
v v27 Sub32 t5 0 - p2:21:10:0:0 2 v26,v8
v v31 Store t31 0 a7 p2:21:10:0:0 3 v25,v27,v22
v v36 Load t5 0 - p2:22:21:1:0 1 v13,v31
v v43 Load t5 0 - p2:22:34:0:0 1 v10,v31
v v37 Add32 t5 0 - p2:22:24:0:0 2 v36,v8
v v44 Add32 t5 0 - p2:22:37:0:0 2 v43,v8
v v12 Store t31 0 a7 p2:22:8:0:0 1 v13,v37,v31
v v9 Store t31 0 a7 p2:22:8:0:0 3 v10,v44,v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 Load t20 0 - p2:23:9:1:0 1 v2,v9
v v42 Load t15 0 - p2:23:9:1:0 1 v35,v9
v v35 OffPtr t23 24 - p2:23:9:1:0 1 v19
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 33 "lower"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 10 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 3 v19,v27,v22
v v36 ARM64MOVWload t5 8 - p2:22:21:1:0 1 v19,v31
v v43 ARM64MOVWload t5 12 - p2:22:34:0:0 1 v19,v31
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v36,v8
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v43,v8
v v12 ARM64MOVWstore t31 8 - p2:22:8:0:0 1 v19,v37,v31
v v9 ARM64MOVWstore t31 12 - p2:22:8:0:0 3 v19,v44,v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 ARM64MOVDload t20 16 - p2:23:9:1:0 1 v19,v9
v v42 ARM64MOVDload t15 24 - p2:23:9:1:0 1 v19,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v35,v25,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 34 "addressing modes"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 10 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 3 v19,v27,v22
v v36 ARM64MOVWload t5 8 - p2:22:21:1:0 1 v19,v31
v v43 ARM64MOVWload t5 12 - p2:22:34:0:0 1 v19,v31
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v36,v8
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v43,v8
v v12 ARM64MOVWstore t31 8 - p2:22:8:0:0 1 v19,v37,v31
v v9 ARM64MOVWstore t31 12 - p2:22:8:0:0 3 v19,v44,v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 ARM64MOVDload t20 16 - p2:23:9:1:0 1 v19,v9
v v42 ARM64MOVDload t15 24 - p2:23:9:1:0 1 v19,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v35,v25,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 35 "late lower"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 10 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 3 v19,v27,v22
v v36 ARM64MOVWload t5 8 - p2:22:21:1:0 1 v19,v31
v v43 ARM64MOVWload t5 12 - p2:22:34:0:0 1 v19,v31
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v36,v8
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v43,v8
v v12 ARM64MOVWstore t31 8 - p2:22:8:0:0 1 v19,v37,v31
v v9 ARM64MOVWstore t31 12 - p2:22:8:0:0 3 v19,v44,v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 ARM64MOVDload t20 16 - p2:23:9:1:0 1 v19,v9
v v42 ARM64MOVDload t15 24 - p2:23:9:1:0 1 v19,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v35,v25,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 36 "pair"
type t41 TUPLE ? ? ? - "int32,int32" "" t5 t5
type t42 TUPLE ? ? ? - "*uint8,int" "" t20 t15
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v36,v8
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v43,v8
v v12 ARM64STPW t31 8 - p2:22:8:0:0 1 v19,v37,v44,v31
v v9 Copy t31 0 - p2:22:8:0:0 2 v12
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v9
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v9
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v36,v8
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v43,v8
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:20:23
dcllen 4
end
pass 38 "lowered cse"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
dcllen 4
end
pass 39 "elim unread autos"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
dcllen 4
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
dcllen 4
end
pass 41 "lowered deadcode"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
dcllen 4
end
pass 42 "checkLower"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
dcllen 4
end
pass 43 "loop invariant"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
dcllen 4
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
dcllen 4
end
pass 45 "tighten"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
dcllen 4
end
pass 46 "late deadcode"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
dcllen 4
end
pass 47 "critical"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
dcllen 4
end
pass 48 "phi tighten"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
dcllen 4
end
pass 49 "likelyadjust"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
dcllen 4
end
pass 50 "layout"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 1 -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v19 ARM64LoweredNilCheck t2 0 - p2:20:3:1:0 7 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v19,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v19,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v19,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v19,v27,v22
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v19,v37,v44,v31
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v19,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v19,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
fstate laidout
dcllen 4
end
pass 51 "schedule"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 8 -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v19 ARM64LoweredNilCheck t33 0 - p2:20:3:1:0 0 v7,v1
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v7,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v7,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v7,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v7,v27,v22
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v7,v31
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v7,v37,v44,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v7,v12
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
fstate scheduled,laidout
dcllen 4
end
pass 52 "late nilcheck"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 7 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v7,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v7,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v7,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v7,v27,v22
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v7,v31
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v7,v37,v44,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v7,v12
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
fstate scheduled,laidout
dcllen 4
end
pass 53 "flagalloc"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 7 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v7,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v7,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v7,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v7,v27,v22
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v7,v31
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v7,v37,v44,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v7,v12
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v18,v27,v37,v44,v54,v42,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v9,v16,v13,v10,v2,v50,v55,v57,v59,v61,v51,v5,v3,v53,v56,v58,v60,v14,v23,v28,v33,v40,v47,v30,v21,v4,v6,v49,v48,v46,v45,v41,v39,v38,v34,v32,v29,v24,v20,v15,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
fstate scheduled,laidout
dcllen 4
end
pass 54 "regalloc"
aux a1 call "AuxCall{main.grow}" a2 1 2 1 8 16 2 6
abiparam in 0 t2 a3 0 0
abiparam in 1 t5 a4 1 8
abiparam out 0 t3 a5 0,1,2,3,4,5 -1
callreg 0:1,1:2,2:4,3:8,4:10,5:20 - 0 -
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 7 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v7,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v7,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v7,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v7,v27,v22
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v7,v31
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v7,v37,v44,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v7,v12
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v9 Copy t5 0 - p2:23:2:2:0 1 v18
v v16 Copy t5 0 - p2:23:2:2:0 1 v27
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v9,v16,v37,v44,v54,v42,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v2,v3,v4,v5,v6,v10,v11,v13,v14,v15,v20,v21,v23,v24,v28,v29,v30,v32,v33,v34,v38,v39,v40,v41,v45,v46,v47,v48,v49,v50,v51,v53,v55,v56,v57,v58,v59,v60,v61
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
fstate scheduled,laidout
regalloc 55 v7:R0,v8:R1,v9:R0,v16:R1,v17:R6,v18:R6,v25:(R4;R5),v26:R7,v27:R7,v35:(R8;R9),v36:R8,v37:R2,v42:R5,v43:R9,v44:R3,v52:[],v54:R4
dcllen 4
end
pass 55 "loop rotate"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 7 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v7,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v7,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v7,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v7,v27,v22
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v7,v31
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v7,v37,v44,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v7,v12
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v9 Copy t5 0 - p2:23:2:2:0 1 v18
v v16 Copy t5 0 - p2:23:2:2:0 1 v27
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v9,v16,v37,v44,v54,v42,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v2,v3,v4,v5,v6,v10,v11,v13,v14,v15,v20,v21,v23,v24,v28,v29,v30,v32,v33,v34,v38,v39,v40,v41,v45,v46,v47,v48,v49,v50,v51,v53,v55,v56,v57,v58,v59,v60,v61
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
fstate scheduled,laidout
regalloc 55 v7:R0,v8:R1,v9:R0,v16:R1,v17:R6,v18:R6,v25:(R4;R5),v26:R7,v27:R7,v35:(R8;R9),v36:R8,v37:R2,v42:R5,v43:R9,v44:R3,v52:[],v54:R4
dcllen 4
end
pass 56 "trim"
f b1 t1 a1 61 1
b b1 Ret p2:23:9:1:0 0 0 - v52 - -
v v8 ArgIntReg t5 1 a10 p2:23:9:1:0 4 -
v v7 ArgIntReg t2 0 a9 p2:23:9:1:0 7 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v17 ARM64MOVWload t5 0 - p2:20:7:1:0 1 v7,v1
v v18 ARM64SUB t5 0 - p2:20:10:0:0 2 v17,v8
v v22 ARM64MOVWstore t31 0 - p2:20:10:0:0 2 v7,v18,v1
v v26 ARM64MOVWload t5 4 - p2:21:7:1:0 1 v7,v22
v v27 ARM64SUB t5 0 - p2:21:10:0:0 2 v26,v8
v v31 ARM64MOVWstore t31 4 - p2:21:10:0:0 2 v7,v27,v22
v v35 ARM64LDPSW t41 8 - p2:22:21:1:0 2 v7,v31
v v36 Select0 t5 0 - p2:22:21:1:0 1 v35
v v43 Select1 t5 0 - p2:22:34:0:0 1 v35
v v37 ARM64ADD t5 0 - p2:22:24:0:0 2 v8,v36
v v44 ARM64ADD t5 0 - p2:22:37:0:0 2 v8,v43
v v12 ARM64STPW t31 8 - p2:22:8:0:0 2 v7,v37,v44,v31
v v25 ARM64LDP t42 16 - p2:23:9:1:0 2 v7,v12
v v42 Select1 t15 0 - p2:23:9:1:0 1 v25
v v54 Select0 t20 0 - p2:23:9:1:0 1 v25
v v9 Copy t5 0 - p2:23:2:2:0 1 v18
v v16 Copy t5 0 - p2:23:2:2:0 1 v27
v v52 MakeResult t40 0 - p2:23:2:1:0 1 v9,v16,v37,v44,v54,v42,v12
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2
consts -
freev v2,v3,v4,v5,v6,v10,v11,v13,v14,v15,v20,v21,v23,v24,v28,v29,v30,v32,v33,v34,v38,v39,v40,v41,v45,v46,v47,v48,v49,v50,v51,v53,v55,v56,v57,v58,v59,v60,v61
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 2:20:23
fstate scheduled,laidout
regalloc 55 v7:R0,v8:R1,v9:R0,v16:R1,v17:R6,v18:R6,v25:(R4;R5),v26:R7,v27:R7,v35:(R8;R9),v36:R8,v37:R2,v42:R5,v43:R9,v44:R3,v52:[],v54:R4
dcllen 4
end
frontend
end
ptrcache t3,t5,t6,t9,t10,t11,t13,t15,t16,t17,t19,t20,t27,t39
typelink t31=t35
typeorder t8,t11,t9,t12,t5,t13,t10,t14,t15,t18,t19,t28,t29,t16,t17,t7,t20,t21,t22,t23,t24,t25,t26,t27,t36,t2,t37,t39,t1,t3,t4,t6,t30,t31,t33,t32,t34,t41,t42,t35,t38,t40
eof
"#

/-- `examples/structs/main/grow,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "grow" 1
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
type t1 8 8 8 1 01 "*rect"
name n1 "r" PPARAM t1 1 "main.r" 0 a3
type t2 4 4 0 0 - "int32"
name n2 "d" PPARAM t2 1 "main.d" 0 a4
type t3 32 8 24 1 04 "rect"
name n3 "~r0" PPARAMOUT t3 1 "main.~r0" 0 a5
type t4 8 4 0 0 - "point"
name n4 ".autotmp_3" PAUTO t4 3 "main..autotmp_3" 0 -
in n1 0 used
in n2 8 used
in n3 0 outregs
in n4 0 used,autotmp
out n1 0 used
out n2 8 used
opt n3 0 outregs
opt n4 0 autotmp
stack 0 0 8
end
genin
posbase p2 "./main.go" 1 1 -1 1 "./main.go" "./main.go" 1 1
sym y1 "main.grow" 1
curfn p2:19:6:0:0 0 0
regargs 8192:0:t1,8193:8:t2
text y1 0 0 0 0 19 200080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "main.grow.arginfo1" 0
sym y5 "main.grow.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 0 p2:19:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:19:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:19:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:19:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:19:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:19:6:2:0
p 6 6 0 0 0 - MOVW 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8198/0/0/NONE/0/0/-/- 0 0 p2:20:7:1:0
p 7 7 0 0 0 - SUB 0 REG/8193/0/0/NONE/0/0/-/- 8198 - REG/8198/0/0/NONE/0/0/-/- 0 0 p2:20:10:2:0
p 8 8 0 0 0 - MOVW 0 REG/8198/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 0 0 p2:20:10:2:0
p 9 9 0 0 0 - MOVW 0 MEM/8192/0/0/NONE/0/4/-/- 0 - REG/8199/0/0/NONE/0/0/-/- 0 0 p2:21:7:1:0
p 10 10 0 0 0 - SUB 0 REG/8193/0/0/NONE/0/0/-/- 8199 - REG/8199/0/0/NONE/0/0/-/- 0 0 p2:21:10:2:0
p 11 11 0 0 0 - MOVW 0 REG/8199/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/4/-/- 0 0 p2:21:10:2:0
p 12 12 0 0 0 - LDPSW 0 MEM/8192/0/0/NONE/0/8/-/- 0 - REGREG/8200/0/0/NONE/0/8201/-/- 0 0 p2:22:21:1:0
p 13 13 0 0 0 - ADD 0 REG/8200/0/0/NONE/0/0/-/- 8193 - REG/8194/0/0/NONE/0/0/-/- 0 0 p2:22:21:2:0
p 14 14 0 0 0 - ADD 0 REG/8201/0/0/NONE/0/0/-/- 8193 - REG/8195/0/0/NONE/0/0/-/- 0 0 p2:22:37:2:0
p 15 15 0 0 0 - STPW 0 REGREG/8194/0/0/NONE/0/8195/-/- 0 - MEM/8192/0/0/NONE/0/8/-/- 0 0 p2:22:8:2:0
p 16 16 0 0 0 - LDP 0 MEM/8192/0/0/NONE/0/16/-/- 0 - REGREG/8196/0/0/NONE/0/8197/-/- 0 0 p2:23:9:1:0
p 17 17 0 0 0 - MOVD 0 REG/8198/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:23:2:2:0
p 18 18 0 0 0 - MOVD 0 REG/8199/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:23:2:2:0
p 19 19 0 0 0 - RET 0 _ 0 - _ 0 0 p2:23:9:2:0
p 20 20 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 19 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
spill MEM/8383/0/0/NONE/0/16/-/- 8193 0 MOVW MOVW
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
dbgloc 0 1:-10000:1:9:50
dbgloc 1 1:-10000:1:16:51
dbgregout n3
dbgpc 1:9:18,1:16:19
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 2 p2:19:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:19:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:19:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:19:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p2:19:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:19:6:2:0
p 6 0 0 0 392 - MOVW 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8198/0/0/NONE/2/0/-/- 0 0 p2:20:7:1:0
p 7 4 0 0 23 - SUB 0 REG/8193/0/0/NONE/2/0/-/- 8198 - REG/8198/0/0/NONE/2/0/-/- 0 0 p2:20:10:2:0
p 8 8 0 0 375 - MOVW 0 REG/8198/0/0/NONE/2/0/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 0 0 p2:20:10:2:0
p 9 12 0 0 392 - MOVW 0 MEM/8192/0/0/NONE/88/4/-/- 0 - REG/8199/0/0/NONE/2/0/-/- 0 0 p2:21:7:1:0
p 10 16 0 0 23 - SUB 0 REG/8193/0/0/NONE/2/0/-/- 8199 - REG/8199/0/0/NONE/2/0/-/- 0 0 p2:21:10:2:0
p 11 20 0 0 375 - MOVW 0 REG/8199/0/0/NONE/2/0/-/- 0 - MEM/8192/0/0/NONE/88/4/-/- 0 0 p2:21:10:2:0
p 12 24 0 0 262 - LDPSW 0 MEM/8192/0/0/NONE/87/8/-/- 0 - REGREG/8200/0/0/NONE/7/8201/-/- 0 0 p2:22:21:1:0
p 13 28 0 0 23 - ADD 0 REG/8200/0/0/NONE/2/0/-/- 8193 - REG/8194/0/0/NONE/2/0/-/- 0 0 p2:22:21:2:0
p 14 32 0 0 23 - ADD 0 REG/8201/0/0/NONE/2/0/-/- 8193 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:22:37:2:0
p 15 36 0 0 453 - STPW 0 REGREG/8194/0/0/NONE/7/8195/-/- 0 - MEM/8192/0/0/NONE/87/8/-/- 0 0 p2:22:8:2:0
p 16 40 0 0 245 - LDP 0 MEM/8192/0/0/NONE/86/16/-/- 0 - REGREG/8196/0/0/NONE/7/8197/-/- 0 0 p2:23:9:1:0
p 17 44 0 0 301 - MOVD 0 REG/8198/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:23:2:2:0
p 18 48 0 0 301 - MOVD 0 REG/8199/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:23:2:2:0
p 19 52 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:23:9:2:0
fn y1 16 0 0 0 19 2000c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
spill MEM/8383/0/0/NONE/0/16/-/- 8193 0 MOVW MOVW
funcaux y2 y3 - - y4 y5 -
text 64 0 060080b9c60001cb060000b9070480b9e70001cb070400b9082441692200088b2300098b020c0129041441a9e00306aae10307aac0035fd60000000000000000 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y3,_,_,_,y4,y5
usedfiles 1
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 5 1 8000 00080804ff 0
data y5 SDATA 2 1 8000 0000 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 041000 0
data y10 SRODATA 3 1 28000 021000 0
data y11 SRODATA 3 1 28000 041000 0
data y12 SRODATA 9 1 28000 2a0302030204020600 0
data y13 SRODATA 3 1 28000 001000 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "go:info.*main.rect" 0
sym y19 "go:info.int32" 0
sym y20 "go:info.main.rect" 0
sym y21 "type:main.rect" 0
dwfn y14 y15 y16 - y17 "main.grow" 1:19 1 0 1 5
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2,n3
dwname n1 1 1 0 0 0 0 0 0 - - "*main.rect" 0 0 1 p2:19:11:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "int32" 0 0 1 p2:19:20:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "main.rect" 0 0 1 p2:19:29:0:0
dwname n4 1 0 1 0 0 0 0 0 - - "main.point" 0 0 1 p2:22:15:0:0
var 0 0 "r" 5 1 0 0 0 8 y18 "./main.go" 19 11 0 0 0 0 v0
var 1 0 "d" 5 1 0 0 0 16 y19 "./main.go" 19 20 0 1 0 0 v1
var 2 0 "~r0" 5 1 1 0 0 0 y20 "./main.go" 19 29 0 2 0 0 -
scope 0 0 - 0,1,2
data y14 SDWARFFCN 60 0 0 036d61696e2e67726f77000040019c0200000013012d7200001300000000000000002d6400001300000000000000002e7e7230000113000000000000 7
reloc 0 0 R_USETYPE 0 y21
reloc 11 1 R_DWTXTADDR_U1 0 y1
reloc 26 4 R_DWARFSECREF 0 y18
reloc 30 4 R_DWARFSECREF 0 y15
reloc 39 4 R_DWARFSECREF 0 y19
reloc 43 4 R_DWARFSECREF 8 y15
reloc 54 4 R_DWARFSECREF 0 y20
data y15 SDWARFLOC 16 0 0 01000400300150000100040034015100 2
reloc 1 1 R_DWTXTADDR_U1 0 y1
reloc 9 1 R_DWTXTADDR_U1 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 35 0 0 00090200000000000000000402030e1406370660063706600637068806370214000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `main.grow`. -/
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

def blk : Block := (lc.ctx.f.block? 1).getD default

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

/-- The PC table of the block walk (`b1`: `v12`'s `STPW` at Prog 15). -/
def tab : PcTab :=
  match c2.blocks lc.ctx.f.blocks.toList with
  | .ok t => t
  | .error _ => []

/-- The class table of G55's check (`kFlow`). -/
def kt : KTab :=
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)

/-- The class map before `v12` (index 14 of `b1`). -/
def K : KMap := kAt lc kt 1 blk 14

/-- A value check's answer `r` is one Prog's pattern, which Prog `k` of `qs` matches. -/
def vkOK (r : Option (Except String VKind2)) (qs : Array GoFV.Asm.Prog) (k : Nat) : Bool :=
  match r with
  | some (.ok (.prog p)) => decide (k < qs.size) && p.ok (qs[k]?.getD default)
  | _ => false

theorem vkOK_spec {r : Option (Except String VKind2)} {qs : Array GoFV.Asm.Prog} {k : Nat}
    (h : vkOK r qs k = true) :
    ∃ p, r = some (.ok (.prog p)) ∧ ∃ hk : k < qs.size, p.ok qs[k] = true := by
  match r, h with
  | some (.ok (.prog p)), h =>
    simp only [vkOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hk, hok⟩ := h
    rw [Array.getElem?_eq_getElem hk, Option.getD_some] at hok
    exact ⟨p, rfl, hk, hok⟩
  | none, h => cases h
  | some (.error _), h => cases h
  | some (.ok .entry), h => cases h
  | some (.ok .none), h => cases h
  | some (.ok (.progs _)), h => cases h

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- The machine address of `heap 1`, the struct `p` points to (its Phase 1 address `2^41`). -/
def A : BitVec 64 := 0x20000000000

/-- `ι`: the nil block, the globals at `symA`, `heap 1` at `A`. -/
def ι57 : Blk → Option (BitVec 64)
  | .nil => some 0
  | .global _ => some GenG2.symA
  | .heap 1 => some 0x20000000000
  | _ => none

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `A` and the PC table of the block walk. -/
def E : MatchEnv :=
  { lc, ι := ι57, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The struct `p` (`v7`): the start of `heap 1`. -/
def pD : Ptr := ⟨.heap 1, 0⟩

/-- The new `p.x` (`v37`) and `p.y` (`v44`); `y < 2^8`, so that the word the two make at offset 8
is below `2^40` and encodes no pointer address. -/
def xIn : BitVec 32 := 0x11223344
def yIn : BitVec 32 := 0x55

/-- The Phase 1 memory before `v12`: `heap 1`, 32 poison bytes. -/
def mem1 : Mem :=
  { blocks := #[(.heap 1, { data := Array.replicate 32 .poison })], nextHeap := 2 }

/-- The `runLoc` state before `v12`: `p` (`pD`) in `R0`, `x` in `R2`, `y` in `R3`, every other
register `poison`, the memory `mem1`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 0 then .ptr pD else if i.val = 2 then .int .w32 xIn
      else if i.val = 3 then .int .w32 yIn else .poison,
    flags := .poison, slots := [], mem := .mem mem1 }

/-- The machine before `v12`: `X0 = A`, `X2`, `X3` the two words with nonzero upper halves (the
store keeps only the low words), the activation's `g` and `FP`, the PC of `v12`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 0 then A else if k = 2 then 0xdead000011223344
      else if k = 3 then 0xbeef000000000055 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 14, mem := fun _ => 0 }

/-- A home in a register (other than `ZR`) has a width class, for every home of `lc`. -/
def homesOK (lc : LocCtx) : Bool :=
  (List.range lc.homes.size).all fun i => match lc.home i with
    | some (.reg r) => r == zeroReg || (cls (lc.ty i)).isSome
    | _ => true

/-- After `v12`: the memory's first block is `heap 1`, with `x`'s low byte `0x44` at offset 8 and
no pointer word starting at offsets 0 to 8. -/
def memIs (s : LocState) : Bool :=
  match s.mem with
  | .mem mm =>
    match mm.blocks[0]? with
    | some (b, al) => b == .heap 1 && al.data[8]? == some (.b 0x44) &&
        (List.range 9).all fun o => (ptrWordAt? al.data o).isNone
    | none => false
  | _ => false

theorem memIs_spec {s : LocState} (h : memIs s = true) :
    ∃ mm al, s.mem = .mem mm ∧ (Blk.heap 1, al) ∈ mm.blocks ∧ al.data[8]? = some (.b 0x44) ∧
      ∀ o, o < 9 → ptrWordAt? al.data o = none := by
  unfold memIs at h
  split at h
  · rename_i mm hm
    split at h
    · rename_i b al hba
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
        Option.isNone_iff_eq_none] at h
      obtain ⟨⟨rfl, h8⟩, hp⟩ := h
      exact ⟨mm, al, hm, Array.mem_of_getElem? hba, h8, hp⟩
    · cases h
  · cases h

/-- What compiled evaluation checks on `main.grow`: G55's check rejects it (`v12: op STPW`); the
block walk with `vkind57a` (`vkW`) succeeds with `tab`, where `v12` (index 14 of `b1`) starts at
Prog 15 and the next value at Prog 16; the frame check passes, the function accesses no frame
variable and has no home slot, its Prog IDs are distinct and below `2^32` and every register home
has a width class; `v12` is `STPW [8] v7 v37 v44 v31`, which `vkind57a` accepts with a pattern
Prog 15 matches; the class map before it gives `R0` 64 bits and `R2`, `R3` 32 bits and holds its
reads; `stepLoc` runs `v12` from `s0` to a memory with `x`'s low byte at `heap 1 + 8`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered && (checkG55 lc0 ps bs g).toOption.isNone &&
    (c2.blocks lc.ctx.f.blocks.toList).toOption.isSome &&
    ((tab.lookup 1).getD []).getD 14 0 == 15 && ((tab.lookup 1).getD []).getD 15 0 == 16 &&
    (match checkFrame lc g with | .ok _ => true | .error _ => false) &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    ps.toList.all (·.id < 2 ^ 32) && decide ((ps.toList.map (·.id)).Nodup) && homesOK lc &&
    (lc.ctx.f.value? 12).isSome && blk.values[14]? == some 12 && (val 12).op == .ARM64STPW &&
    vkOK (vkind57a lc g (val 12)) ps 15 &&
    (kReads lc (val 12)).all (fun rc => K.get rc.1 == some rc.2) &&
    K.get 0 == some 64 && K.get 2 == some 32 && K.get 3 == some 32 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 12)) memIs

theorem g57a_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ (checkG55 lc0 ps bs g).toOption = none ∧
      ((tab.lookup 1).getD []).getD 14 0 = 15 ∧ ((tab.lookup 1).getD []).getD 15 0 = 16 ∧
      checkFrame lc g = .ok () ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧ homesOK lc = true ∧
      lc.ctx.f.value? 12 = some (val 12) ∧ blk.values[14]? = some 12 ∧
      (val 12).op = .ARM64STPW ∧ vkOK (vkind57a lc g (val 12)) ps 15 = true ∧
      (∀ rc ∈ kReads lc (val 12), K.get rc.1 = some rc.2) ∧
      K.get 0 = some 64 ∧ K.get 2 = some 32 ∧ K.get 3 = some 32 ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 12)) memIs = true := by
  have hf := g57a_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Option.isNone_iff_eq_none, and_assoc] at hf
  obtain ⟨hl, h55, -, h14, h15, hcf, hav, hsl, hlt, hnd, hho, hv, hi, hop, hvk, hrd, hk0, hk2,
    hk3, hrun⟩ := hf
  refine ⟨hl, h55, h14, h15, ?_, hav, hsl, ?_, hnd, hho, ?_, hi, hop, hvk, ?_, hk0, hk2, hk3,
    hrun⟩
  · revert hcf; cases checkFrame lc g <;> simp
  · exact fun p hp => by simpa using List.all_eq_true.1 hlt p hp
  · obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.1 hv
    simp [val, hv']
  · exact fun rc hrc => by simpa using List.all_eq_true.1 hrd rc hrc

/-! ## The activation -/

/-- `ι57` puts every block with a Phase 1 address (`nil`, `heap 1`) at it. -/
theorem addrAgree57 : AddrAgree ι57 := by
  intro b n a hb ha _
  cases b with
  | nil => simp [ι57] at ha; simp [Blk.base?] at hb; subst hb; subst ha; rfl
  | heap k =>
    simp only [Blk.base?_heap, Option.some.injEq] at hb
    subst hb
    unfold ι57 at ha
    split at ha <;> first | cases ha | skip
    all_goals simp_all
  | _ => simp [ι57] at ha <;> simp [Blk.base?] at hb

theorem clsReg0 {lc : LocCtx} (h : homesOK lc = true) :
    ∀ i r, lc.home i = some (.reg r) → r ≠ zeroReg → (cls (lc.ty i)).isSome = true := by
  intro i r hh hr
  by_cases hi : i < lc.homes.size
  · have := List.all_eq_true.1 h i (List.mem_range.2 hi)
    rw [hh] at this
    simp only [Bool.or_eq_true, beq_iff_eq, hr, false_or] at this
    exact this
  · have hn : lc.home i = none := by
      simp only [LocCtx.home]
      rw [getElem?_neg lc.homes i hi]
      rfl
    rw [hn] at hh
    cases hh

theorem g57aEnv (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32)
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
            retOut := fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := addrAgree57
            glob := fun _ _ _ _ => rfl
            syms := by
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

/-! ## The memory -/

theorem mem1_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ mem1.blocks) :
    b = .heap 1 ∧ al = { data := Array.replicate 32 .poison } := by
  simpa [mem1] using h

/-- `mem1` injected into the zero memory by `ι57`: `heap 1`'s poison bytes at `A`. -/
theorem memInj1 : MemInj ι57 mem1 (fun _ => 0) where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    exact ⟨A, rfl, fun _ => by decide, by simp [A]⟩
  inj := by
    intro b al b' al' a a' h h' hne _ _
    obtain ⟨rfl, -⟩ := mem1_blocks h
    obtain ⟨rfl, -⟩ := mem1_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h _ => ?_⟩
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    simp [ByteRel]

theorem keys1 : KeysNodup mem1 := by simp [KeysNodup, mem1]

theorem sep1 : SepFrom ι57 (StkAt E) mem1 := by
  intro b al a h ha y hy
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    rw [hsp] at h2
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    have ha' : a = A := by simp [ι57] at ha; exact ha.symm
    subst ha'
    have hA : A.toNat = 0x20000000000 := rfl
    simp only [hA, Array.size_replicate]
    omega
  · cases hk

/-! ## `v12`: `STPW (R2, R3), 8(R0)` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .ptr pD) ∨ (r = 2 ∧ x = .int .w32 xIn) ∨ (r = 3 ∧ x = .int .w32 yIn) ∨
      x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · split at h
      · rename_i _ h2; exact Or.inr (Or.inl ⟨h2, h.symm⟩)
      · split at h
        · rename_i _ _ h3; exact Or.inr (Or.inr (Or.inl ⟨h3, h.symm⟩))
        · exact Or.inr (Or.inr (Or.inr h.symm))
  · cases h

theorem locMatch0 : LocMatch E s0 1 14 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact ⟨A, rfl, by decide⟩
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show (m0.x 2).setWidth 32 = xIn
      decide
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show (m0.x 3).setWidth 32 = yIn
      decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem1, rfl, memInj1⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g57aInv0 (h0 : K.get 0 = some 64) (h2 : K.get 2 = some 32) (h3 : K.get 3 = some 32) :
    G3Inv E lc K s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem1, rfl, keys1, sep1⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · rw [h2] at hc; cases hc; rfl
    · rw [h3] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- **G57, group A, on `main.grow`** (`examples/structs`: `func grow(r *rect, d int32) rect {
r.min.x -= d; r.min.y -= d; r.max = point{r.max.x + d, r.max.y + d}; return *r }`, whose two
32-bit stores of `r.max` are one `STPW`): `b1`'s `v12` (`STPW [8] v7 v37 v44 v31`, `r` in `R0`,
the new `r.max.x`, `r.max.y` in `R2`, `R3`), which `checkG55` rejects (`v12: op STPW`) and
`vkind57a` accepts. From `s0`, with `heap 1` (32 poison bytes) in `R0`, `x = 0x11223344` in `R2`
and `y = 0x55` in `R3`, `stepLoc` runs `v12` to a memory with `x`'s low byte `0x44` at
`heap 1 + 8`, and `vk57a_step` relates it to a machine state after Prog 15 (`STPW (R2, R3),
8(R0)`) whose memory holds `0x44` at `A + 8` although `X2`'s upper half is not zero, under an
activation extending `E` that is again a `G49Env`. -/
theorem genG57a_witness :
    (checkG55 lc0 ps bs g).toOption = none ∧
      ∃ s1 mm E1 m1, stepLoc GenG2.env lc s0 (val 12) = .ok s1 ∧ s1.mem = .mem mm ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 15 m1 ∧ m1.mem (A + BitVec.ofNat 64 8) = 0x44 := by
  obtain ⟨hl, h55, h14, h15, hcf, hav, hsl, hlt, hnd, hho, hv, hi, hop, hvk, hrd, hk0, hk2, hk3,
    hrun⟩ := facts
  obtain ⟨pt, hvk, hk15, hok⟩ := vkOK_spec hvk
  obtain ⟨s1, hs1, hd⟩ := GenG1.okThen_spec hrun
  obtain ⟨mm, al, hmm, hal, hal8, hpw⟩ := memIs_spec hd
  have hE := g57aEnv hlt hav hsl
  have F : Facts lc (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList 0 E :=
    ⟨hl, clsReg0 hho, hnd, hlt,
      fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp), addrAgree57⟩
  obtain ⟨htemp, hVK⟩ := vkind57a_spec hvk
  have hvs : VStep2 ps (.prog pt) 15 16 :=
    ⟨15, Nat.le_refl _, rfl, hk15, hok, fun l _ h1 h2 => absurd h2 (by omega)⟩
  have hj : E.pcOf 1 14 = pcAt GenG2.text ps.toList 15 := by
    show pcOfTab GenG2.text ps.toList tab 1 14 = _
    unfold pcOfTab; rw [h14]
  have hj' : E.pcOf 1 (14 + 1) = pcAt GenG2.text ps.toList 16 := by
    show pcOfTab GenG2.text ps.toList tab 1 15 = _
    unfold pcOfTab; rw [h15]
  have hpre : PairPre50 lc s0 (val 12) := by
    intro _ _ _ _ hpo; rw [hop] at hpo; simp [pairOp50] at hpo
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := vk57a_step (H := GenG2.H0) (env := GenG2.env)
    (L := []) hE F hcf hv hVK hvs htemp hj hj' hrd locMatch0 (g57aInv0 hk0 hk2 hk3)
    (fun _ h => by cases h) hpre hs1
  -- Byte 8 of `heap 1` after the store, read through `MemInj`: no pointer word covers it.
  have hA : m1.mem (A + BitVec.ofNat 64 8) = 0x44 := by
    obtain ⟨mm1, hmm1, hinj⟩ := hm1'.mem
    rw [hmm] at hmm1
    cases hmm1
    obtain ⟨W, hW⟩ := hinj.bytes
    obtain ⟨hw, -, hby⟩ := hW _ _ _ hal (hx1.2 (.heap 1) A rfl)
    obtain ⟨h8, hd8⟩ := Array.getElem?_eq_some_iff.1 hal8
    have hr := hby 8 h8 (fun o ho ho' => by
      obtain ⟨p, hp, -⟩ := hw o ho
      rw [hpw o (by omega)] at hp
      cases hp)
    rw [hd8] at hr
    exact hr.symm
  exact ⟨h55, s1, mm, E1, m1, hs1, hmm, hx1, hE1, hp1, hm1', hA⟩

end GoFV.Proof.Witness.GenG57a
