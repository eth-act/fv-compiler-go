import GoFV.Proof.Gen.G43
import GoFV.Proof.Witness.GenG42

namespace GoFV.Proof.Witness.GenG43

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/%28%2AdebugLogWriter%29.varint,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "(*debugLogWriter).varint" 1 1 0
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
type t5 STRUCT 0 1 0 notinheap,comparable,named "sys.nih" "internal/runtime/sys.nih" 0
type t4 STRUCT 0 1 0 notinheap,comparable,named "sys.NotInHeap" "internal/runtime/sys.NotInHeap" 1
field 0 "_" t5 0 0
type t6 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t9 UINT8 1 1 0 comparable,named "byte" "uint8"
type t8 ARRAY 16384 1 0 comparable "[16384]byte" "[16384]uint8" t9 16384
type t7 STRUCT 16384 1 0 notinheap,comparable,named "debugLogBuf" "runtime.debugLogBuf" 2
field 0 "_" t4 0 0
field 1 "b" t8 0 0
type t11 PTR 8 8 0 comparable "*debugLogBuf" "*runtime.debugLogBuf" t7
type t10 STRUCT 40 8 0 comparable,named "debugLogReader" "runtime.debugLogReader" 5
field 0 "data" t11 0 0
field 1 "begin" t6 8 0
field 2 "end" t6 16 0
field 3 "tick" t6 24 0
field 4 "nano" t6 32 0
type t12 ARRAY 10 1 0 comparable "[10]byte" "[10]uint8" t9 10
type t3 STRUCT 16464 8 0 notinheap,comparable,named "debugLogWriter" "runtime.debugLogWriter" 7
field 0 "_" t4 0 0
field 1 "write" t6 0 0
field 2 "data" t7 8 0
field 3 "tick" t6 16392 0
field 4 "nano" t6 16400 0
field 5 "r" t10 16408 0
field 6 "buf" t12 16448 0
type t2 PTR 8 8 0 comparable "*debugLogWriter" "*runtime.debugLogWriter" t3
type t13 INT64 8 8 0 comparable,named "int64" "int64"
type t1 FUNC 8 8 8 hasptr,direct "method(*debugLogWriter) func(int64)" "method(*runtime.debugLogWriter) func(int64)" 1 1 0
field 0 "l" t2 ? 0
field 1 "x" t13 ? 0
aux a2 sym "runtime.(*debugLogWriter).varint" "runtime.(*debugLogWriter).varint" 1 - 0 - - - - 0
posbase p122 "runtime/debuglog.go" 1 1 -1
aux a3 name "l" "l" PPARAM t2 0 1 used p122:533:7:0:0
aux a4 name "x" "x" PPARAM t13 8 1 used p122:533:33:0:0
aux a1 call "AuxCall{runtime.(*debugLogWriter).varint}" a2 1 2 0 8 16 2 0
abiparam in 0 t2 a3 0 0
abiparam in 1 t13 a4 1 8
type t14 BOOL 1 1 0 comparable,named "bool" "bool"
type t15 INT8 1 1 0 comparable,named "int8" "int8"
type t16 INT16 2 2 0 comparable,named "int16" "int16"
type t17 INT32 4 4 0 comparable,named "int32" "int32"
type t18 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t19 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t20 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t21 INT 8 8 0 comparable,named "int" "int"
type t22 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t23 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t24 UINT 8 8 0 comparable,named "uint" "uint"
type t25 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t26 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t27 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t18
type t28 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t17
type t29 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t20
type t30 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t21
type t31 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t25
type t32 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t22
type t33 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t23
type t34 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t27
type t35 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t36 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t37 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t38 SSA ? ? ? - "mem" ""
type t39 SSA ? ? ? - "flags" ""
type t40 SSA ? ? ? - "void" ""
type t41 SSA 16 8 ? - "int128" ""
type t42 RESULTS ? ? ? - "mem" "" 1 t38
type t43 PTR 8 8 8 hasptr,direct,comparable "**debugLogWriter" "**runtime.debugLogWriter" t2
type t44 PTR 8 8 8 hasptr,direct,comparable "*int64" "*int64" t13
aux a6 sym "runtime.(*debugLogWriter).uvarint" "runtime.(*debugLogWriter).uvarint" 1 - 0 - - - - 0
aux a5 call "AuxCall{runtime.(*debugLogWriter).uvarint}" a6 1 2 0 8 16 2 0
abiparam in 0 t2 - 0 0
abiparam in 1 t6 - 1 8
slot s1 a3 t2 0 - 0
slot s2 a4 t13 0 - 0
aux a7 name "u" "u" PAUTO t6 0 1 used p122:534:6:0:0
slot s3 a7 t6 0 - 0
f b1 t1 a1 26 4
typs Bool=t14,Int8=t15,Int16=t16,Int32=t17,Int64=t13,UInt8=t18,UInt16=t19,UInt32=t20,UInt64=t6,Int=t21,Float32=t22,Float64=t23,UInt=t24,Uintptr=t25,String=t26,BytePtr=t27,Int32Ptr=t28,UInt32Ptr=t29,IntPtr=t30,UintptrPtr=t31,Float32Ptr=t32,Float64Ptr=t33,BytePtrPtr=t34,Complex64=t35,Complex128=t36,UnsafePtr=t37,Mem=t38,Flags=t39,Void=t40,Int128=t41,ResultMem=t42
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 3 -
v v2 SP t25 0 - p0:0:0:0:0 2 -
v v3 SB t25 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t43 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t44 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v8 Const64 t6 0 - p0:0:0:0:0 0 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:0:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v21 Copy t2 0 - p122:540:11:2:0 1 v6
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v23 Copy t38 0 - p122:540:11:2:0 1 v1
v v24 StaticLECall t42 16 a5 p122:540:11:0:0 1 v21,v22,v23
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:0:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v11 Copy t13 0 - p122:536:16:2:0 1 v7
v v12 Copy t6 0 - p122:536:16:2:0 1 v11
v v13 Com64 t6 0 - p122:536:8:0:0 1 v12
v v15 Lsh64x64 t6 0 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v18 Copy t13 0 - p122:538:15:2:0 1 v7
v v19 Copy t6 0 - p122:538:15:2:0 1 v18
v v20 Lsh64x64 t6 0 - p122:538:18:0:0 1 v19,v14
names s1,s2,s3
named s1 v6,v21
named s2 v7,v11,v18
named s3 v8,v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v8,v9,1=v14,v16
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 3 -
v v2 SP t25 0 - p0:0:0:0:0 2 -
v v3 SB t25 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t43 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t44 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v8 Const64 t6 0 - p0:0:0:0:0 0 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v21 Copy t2 0 - p122:540:11:2:0 1 v6
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v23 Copy t38 0 - p122:540:11:2:0 1 v1
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v21,v22,v23
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v11 Copy t13 0 - p122:536:16:2:0 1 v7
v v12 Copy t6 0 - p122:536:16:2:0 1 v11
v v13 Com64 t6 0 - p122:536:8:1:0 1 v12
v v15 Lsh64x64 t6 0 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v18 Copy t13 0 - p122:538:15:2:0 1 v7
v v19 Copy t6 0 - p122:538:15:2:0 1 v18
v v20 Lsh64x64 t6 0 - p122:538:18:1:0 1 v19,v14
names s1,s2,s3
named s1 v6,v21
named s2 v7,v11,v18
named s3 v8,v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v8,v9,1=v14,v16
freev -
freeb -
cache postorder b2,b3,b4,b1
cache linestarts 122:535:541
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 4 -
v v2 SP t25 0 - p0:0:0:0:0 2 -
v v3 SB t25 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t43 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t44 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p122:533:6:2:0 2 -
v v7 Arg t13 0 a4 p122:533:6:2:0 7 -
v v8 Const64 t6 0 - p0:0:0:0:0 0 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v21 Copy t2 0 - p122:540:11:2:0 0 v6
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v23 Copy t38 0 - p122:540:11:2:0 0 v1
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v11 Copy t13 0 - p122:536:16:2:0 0 v7
v v12 Copy t6 0 - p122:536:16:2:0 0 v7
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 0 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v18 Copy t13 0 - p122:538:15:2:0 0 v7
v v19 Copy t6 0 - p122:538:15:2:0 0 v7
v v20 Lsh64x64 t6 0 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6,v6
named s2 v7,v7,v7
named s3 v8,v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v8,v9,1=v14,v16
freev -
freeb -
cache postorder b2,b3,b4,b1
cache linestarts 122:535:541
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 0 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 0 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache linestarts 122:535:541
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 0 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 0 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache linestarts 122:535:541
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 0 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 0 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache linestarts 122:535:541
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 0 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 0 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache linestarts 122:535:541
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache linestarts 122:535:541
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache linestarts 122:535:541
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache linestarts 122:535:541
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p122:533:6:2:0 1 -
v v7 Arg t13 0 a4 p122:533:6:2:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticLECall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v19,v18,v12,v11,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 20 "expand calls"
aux a8 nameoff "l+0" a3 0
aux a9 nameoff "x+0" a4 0
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v19 SB t25 0 - p0:0:0:0:0 0 -
v v18 SP t25 0 - p0:0:0:0:0 2 -
v v12 OffPtr t43 0 - p0:0:0:0:0 0 v18
v v11 OffPtr t44 0 - p0:0:0:0:0 0 v18
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,v12,v11,1=v14,v16
freev v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 21 "decompose builtin"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v19 SB t25 0 - p0:0:0:0:0 0 -
v v18 SP t25 0 - p0:0:0:0:0 2 -
v v12 OffPtr t43 0 - p0:0:0:0:0 0 v18
v v11 OffPtr t44 0 - p0:0:0:0:0 0 v18
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,v12,v11,1=v14,v16
freev v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v19 SB t25 0 - p0:0:0:0:0 0 -
v v18 SP t25 0 - p0:0:0:0:0 2 -
v v12 OffPtr t43 0 - p0:0:0:0:0 0 v18
v v11 OffPtr t44 0 - p0:0:0:0:0 0 v18
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,v12,v11,1=v14,v16
freev v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
v v19 SB t25 0 - p0:0:0:0:0 0 -
v v18 SP t25 0 - p0:0:0:0:0 2 -
v v12 OffPtr t43 0 - p0:0:0:0:0 0 v18
v v11 OffPtr t44 0 - p0:0:0:0:0 0 v18
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,v12,v11,1=v14,v16
freev v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v11,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v11,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v11,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v11,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v11,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v11,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v11,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v11,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 26 4
b b1 If p122:535:9:0:0 0 0 - v10 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v14 Const64 t24 1 - p0:0:0:0:0 2 -
v v16 Const64 t6 1 - p0:0:0:0:0 1 -
v v10 Less64 t14 0 - p122:535:7:1:0 1 v7,v9
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 StaticCall t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 Com64 t6 0 - p122:536:8:1:0 1 v7
v v15 Lsh64x64 t6 1 - p122:536:19:0:0 1 v13,v14
v v17 Or64 t6 0 - p122:536:25:0:0 1 v15,v16
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 Lsh64x64 t6 1 - p122:538:18:1:0 1 v7,v14
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts 0=v9,1=v14,v16
freev v11,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 33 "lower"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 1 v7
v v15 ARM64SLLconst t6 1 - p122:536:19:0:0 1 v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64SLLconst t6 1 - p122:538:18:1:0 1 v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 3 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 1 v7
v v15 ARM64SLLconst t6 1 - p122:536:19:0:0 1 v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64SLLconst t6 1 - p122:538:18:1:0 1 v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 36 "pair"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 122:535:541
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:-:17:20,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b3:b1,b4:b1,b2:b1
cache sdom b1:-:b4:-:2:23,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8,b2:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b3:b1,b4:b1,b2:b1
cache sdom b1:-:b4:-:2:23,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8,b2:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b3:b1,b4:b1,b2:b1
cache sdom b1:-:b4:-:2:23,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8,b2:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v11,v10,v16,v14,v9,v12,v18,v19,v23,v21,v8,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b3:b1,b4:b1,b2:b1
cache sdom b1:-:b4:-:2:23,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8,b2:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a5 call "AuxCall{runtime.(*debugLogWriter).uvarint}" a6 1 2 0 8 16 2 0
abiparam in 0 t2 - 0 0
abiparam in 1 t6 - 1 8
callreg 0:1,1:2 - 7fffffff97ffffff -
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v2,v3,v4,v5,v8,v9,v10,v11,v12,v14,v16,v18,v19,v21,v23
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b3:b1,b4:b1,b2:b1
cache sdom b1:-:b4:-:2:23,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8,b2:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
fstate scheduled,laidout
regalloc 25 v6:R0,v7:R1,v13:R2,v15:R2,v17:R1,v20:R1,v22:R1,v24:[]
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v2,v3,v4,v5,v8,v9,v10,v11,v12,v14,v16,v18,v19,v21,v23
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b3:b1,b4:b1,b2:b1
cache sdom b1:-:b4:-:2:23,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8,b2:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
fstate scheduled,laidout
regalloc 25 v6:R0,v7:R1,v13:R2,v15:R2,v17:R1,v20:R1,v22:R1,v24:[]
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 26 4
b b1 ARM64TBNZ p122:535:9:1:0 0 63 - v7 b3:0,b4:0 -
v v7 ArgIntReg t13 1 a9 p122:535:9:0:0 4 -
v v6 ArgIntReg t2 0 a8 p122:535:9:0:0 1 -
b b3 Plain p122:536:27:0:0 0 0 - - b2:0 b1:0
v v13 ARM64MVN t6 0 - p122:536:8:1:0 2 v7
v v15 ARM64ADD t6 0 - p122:536:19:0:0 1 v13,v13
v v17 ARM64ORconst t6 1 - p122:536:25:0:0 1 v15
b b4 Plain p122:538:21:0:0 0 0 - - b2:1 b1:1
v v20 ARM64ADD t6 0 - p122:538:18:1:0 1 v7,v7
b b2 Ret p122:541:1:0:0 0 0 - v26 - b3:0,b4:0
v v22 Phi t6 0 - p122:540:11:0:0 1 v17,v20
v v1 InitMem t38 0 - p0:0:0:0:0 1 -
v v24 ARM64CALLstatic t42 16 a5 p122:540:11:1:0 1 v6,v22,v1
v v25 SelectN t38 0 - p122:540:11:0:0 1 v24
v v26 MakeResult t42 0 - p122:541:1:1:0 1 v25
names s1,s2,s3
named s1 v6
named s2 v7
named s3 v17,v20,v22
splits -
canon a3/t2/0/-/0=s1,a4/t13/0/-/0=s2,a7/t6/0/-/0=s3
consts -
freev v2,v3,v4,v5,v8,v9,v10,v11,v12,v14,v16,v18,v19,v21,v23
freeb -
cache postorder b2,b3,b4,b1
cache idom b1:-,b3:b1,b4:b1,b2:b1
cache sdom b1:-:b4:-:2:23,b3:b1:-:b2:11:14,b4:b1:-:b3:5:8,b2:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5
cache linestarts 122:535:541
fstate scheduled,laidout
regalloc 25 v6:R0,v7:R1,v13:R2,v15:R2,v17:R1,v20:R1,v22:R1,v24:[]
dcllen 3
end
frontend
end
ptrcache t3,t6,t7,t8,t9,t10,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t31,t34,t35,t36,t37
typelink t9=t18,t38=t42
typeorder t15,t9=t18,t16,t19,t17,t20,t13,t6,t21,t24,t25,t35,t36,t22,t23,t14,t27,t28,t29,t44,t30,t31,t32,t33,t34,t43,t11,t2,t1,t12,t8,t5,t4,t7,t10,t3,t26,t37,t38,t40,t39,t41,t42
eof
"#

/-- `std/std/runtime/%28%2AdebugLogWriter%29.varint,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "(*debugLogWriter).varint" 1
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
type t1 8 8 0 0 - "*debugLogWriter"
name n1 "l" PPARAM t1 1 "runtime.l" 0 a3
type t2 8 8 0 0 - "int64"
name n2 "x" PPARAM t2 1 "runtime.x" 0 a4
type t3 8 8 0 0 - "uint64"
name n3 "u" PAUTO t3 1 "runtime.u" 0 a7
in n1 0 used
in n2 8 used
in n3 0 used
out n1 0 used
out n2 8 used
opt n3 0 -
stack 0 0 8
end
genin
posbase p122 "runtime/debuglog.go" 1 1 -1 119 "runtime/debuglog.go" "runtime/debuglog.go" 1 1
sym y1 "runtime.(*debugLogWriter).varint" 1
curfn p122:533:6:0:0 0 0
regargs 8192:0:t1,8193:8:t2
text y1 0 0 0 0 533 200084
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.(*debugLogWriter).varint.arginfo1" 0
sym y4 "runtime.(*debugLogWriter).varint.argliveinfo" 0
sym y5 "runtime.(*debugLogWriter).uvarint" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i16 0 0 p122:533:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p122:533:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p122:533:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p122:533:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p122:533:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p122:533:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p122:535:9:1:0
p 7 7 0 0 0 - TBZ 0 CONST/0/0/0/NONE/0/63/-/- 8193 - BRANCH/0/0/0/NONE/0/0/-/@12 0 0 p122:535:9:1:0
p 8 8 0 0 0 - MVN 0 REG/8193/0/0/NONE/0/0/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p122:536:8:1:0
p 9 9 0 0 0 - ADD 0 REG/8194/0/0/NONE/0/0/-/- 8194 - REG/8194/0/0/NONE/0/0/-/- 0 0 p122:536:19:2:0
p 10 10 0 0 0 - ORR 0 CONST/0/0/0/NONE/0/1/-/- 8194 - REG/8193/0/0/NONE/0/0/-/- 0 0 p122:536:25:2:0
p 11 11 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@13 0 0 p122:536:27:2:0
p 12 12 0 0 0 - ADD 0 REG/8193/0/0/NONE/0/0/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p122:538:18:1:0
p 13 13 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p122:540:11:1:0
p 14 14 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p122:540:11:1:0
p 15 15 0 0 0 - RET 0 _ 0 - _ 0 0 p122:541:1:0:0
p 16 16 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 533 200084
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgslot 1 n2 t2 0
dbgslot 2 n3 t3 0
dbgvar 0 n1 0
dbgvar 1 n2 1
dbgvar 2 n3 2
dbgloc 0 1:-10000:2:24:50
dbgloc 1 1:-10000:3:17:51
dbgloc 2 3:17:4:-10000:51,4:20:2:24:51
dbgregout -
dbgpc 2:24:15,3:17:11,4:-10000:12,4:20:13
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i16 0 0 p122:533:6:0:0
p 17 0 32 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-32/-/- 0 0 p122:533:6:0:1
p 18 4 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p122:533:6:0:0
p 19 8 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p122:533:6:0:0
p 1 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p122:533:6:0:0
p 2 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p122:533:6:0:0
p 3 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p122:533:6:0:0
p 4 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p122:533:6:0:0
p 5 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p122:533:6:2:0
p 6 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p122:535:9:1:0
p 7 12 0 0 470 - TBZ 0 CONST/0/0/0/NONE/17/63/-/- 8193 - BRANCH/0/0/0/NONE/36/12/-/@12 0 0 p122:535:9:1:0
p 8 16 0 0 405 - MVN 0 REG/8193/0/0/NONE/2/0/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p122:536:8:1:0
p 9 20 0 0 23 - ADD 0 REG/8194/0/0/NONE/2/0/-/- 8194 - REG/8194/0/0/NONE/2/0/-/- 0 0 p122:536:19:2:0
p 10 24 0 0 53 - ORR 0 CONST/0/0/0/NONE/17/1/-/- 8194 - REG/8193/0/0/NONE/2/0/-/- 0 0 p122:536:25:2:0
p 11 28 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/13/-/@13 0 0 p122:536:27:2:0
p 12 32 0 0 23 - ADD 0 REG/8193/0/0/NONE/2/0/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p122:538:18:1:0
p 13 36 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p122:540:11:1:0
p 14 36 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y5/- 0 0 p122:540:11:1:0
p 15 40 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p122:541:1:0:0
p 20 44 -32 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/32/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p122:541:1:0:0
p 21 48 32 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p122:541:1:0:0
fn y1 16 24 0 0 533 200084
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
funcaux y2 y2 - - y3 y4 -
text 64 0 fe0f1ef8fd831ff8fd2300d1a100f8b6e20321aa4200028b410040b2020000142100018b00000094fd835ff8fe0742f8c0035fd6000000000000000000000000 1
reloc 36 4 R_CALLARM64 0 y5
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y2,_,_,_,y3,y4
usedfiles 119
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 5 1 8000 00080808ff 0
data y4 SDATA 2 1 8000 0000 0
data y6 SRODATA 5 1 28000 0003010d00 0
data y7 SRODATA 5 1 28000 0009020700 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 5 1 28000 0003040d00 0
data y10 SRODATA 7 1 28000 0201400b3f0400 0
data y11 SRODATA 4 1 28000 f0011000 0
data y12 SRODATA 14 1 28000 ac08030401020404010401020600 0
data y13 SRODATA 3 1 28000 001000 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "go:info.*runtime.debugLogWriter" 0
sym y19 "go:info.int64" 0
sym y20 "go:info.uint64" 0
dwfn y14 y15 y16 - y17 "runtime.(*debugLogWriter).varint" 119:533 1 0 1 4262
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime.debugLogWriter" 0 0 1 p122:533:7:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "int64" 0 0 1 p122:533:33:0:0
dwname n3 1 0 0 0 0 0 0 0 - - "uint64" 0 0 1 p122:534:6:0:0
var 0 0 "l" 5 1 0 0 0 8 y18 "runtime/debuglog.go" 533 7 0 0 0 0 v0
var 1 0 "x" 5 1 0 0 0 16 y19 "runtime/debuglog.go" 533 33 0 1 0 0 v1
var 2 0 "u" 52 1 0 0 0 -8 y20 "runtime/debuglog.go" 534 6 0 2 0 0 v2
scope 0 0 - 0,1,2
data y14 SDWARFFCN 88 0 0 0372756e74696d652e282a64656275674c6f67577269746572292e766172696e7400000040019c780000009504012d6c0000950400000000000000002d780000950400000000000000002775009604000000000000000000 7
reloc 34 2 R_DWTXTADDR_U2 0 y1
reloc 52 4 R_DWARFSECREF 0 y18
reloc 56 4 R_DWARFSECREF 0 y15
reloc 66 4 R_DWARFSECREF 0 y19
reloc 70 4 R_DWARFSECREF 9 y15
reloc 79 4 R_DWARFSECREF 0 y20
reloc 83 4 R_DWARFSECREF 18 y15
data y15 SDWARFLOC 32 0 0 01000004002801500001000004001c015100010000041c200151042428015100 3
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
reloc 19 2 R_DWTXTADDR_U2 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 31 0 0 000902000000000000000004780a038f041489380637068939380218000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `(*debugLogWriter).varint`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G43's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG43` gives (`b2`: `v22`, `v1`, `v24`, `v25`, `v26`, then the `RET`). -/
def tab : PcTab := [(1, [5, 5, 5]), (3, [8, 9, 10, 11]), (4, [12, 13]), (2, [13, 13, 13, 15, 15, 15])]

/-- The class table `checkG43` gives. -/
def kt : KTab := (match checkG43 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 2).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG43`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `runLoc` state before `v1` (`InitMem`, in `b2`): every register `poison`, the empty
memory, which is the activation's initial memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG37.mem0 },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem GenG37.mem0 }

/-- The machine before `v1`: the activation's `g` and `FP`, the PC of `v1`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 2 1, mem := fun _ => 0 }

/-- What compiled evaluation checks on `(*debugLogWriter).varint`: it holds an arm64 op;
`checkG43` accepts it with `tab` and `kt` and `checkG42` does not; not all its values keep the
memory (the call `v24`); its clean blocks are closed backwards and `(b2, 1)` and `(b2, 2)` are
clean; it accesses no frame variable and has no home slot; `b2` holds `v1` (`InitMem`) at index
1; `stepLoc` runs `v1` from `s0`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG43 lc0 ps bs g).toOption == some (tab, kt) && (checkG42 lc0 ps bs g).toOption.isNone &&
    !memPure lc && cleanOK lc (cleanBlocks lc) && cleanAt lc (cleanBlocks lc) 2 blk 1 &&
    cleanAt lc (cleanBlocks lc) 2 blk 2 && (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 2 && (lc.ctx.f.block? 2).isSome &&
    (lc.ctx.f.value? 1).isSome && blk.values[1]? == some 1 && (val 1).op == .InitMem &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 1)) fun _ => true

theorem g43_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG43 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG42 lc0 ps bs g).toOption = none ∧ memPure lc = false ∧
      cleanOK lc (cleanBlocks lc) = true ∧ cleanAt lc (cleanBlocks lc) 2 blk 1 = true ∧
      cleanAt lc (cleanBlocks lc) 2 blk 2 = true ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      2 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 2 = some blk ∧
      lc.ctx.f.value? 1 = some (val 1) ∧ blk.values[1]? = some 1 ∧ (val 1).op = .InitMem ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 1)) (fun _ => true) = true := by
  have hf := g43_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none, Bool.not_eq_true'] at hf
  obtain ⟨hl, hres, h42, hp, hok, hc1, hc2, hav, hsl, hm1, hbs, hvs, hi1, hop, hrun⟩ := hf
  refine ⟨hl, ?_, h42, hp, hok, hc1, hc2, hav, hsl, hm1, ?_, ?_, hi1, hop, hrun⟩
  · revert hres; cases checkG43 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g43Env (hc : checkG43 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
              checkG43L_spec hl (checkG43_spec hc).2
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
              checkG43L_spec hl (checkG43_spec hc).2
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

/-! ## `v1`: `InitMem` in `b2` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) : x = .poison := by
  simp only [s0, Array.getElem?_replicate] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem locMatch0 : LocMatch E s0 2 1 m0 where
  regs := by
    intro r v hv
    rw [s0_regs hv]
    exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG37.mem0, rfl, GenG37.memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g43Inv0 : G3Inv E lc (kAt lc kt 2 blk 1) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG37.mem0, rfl, by simp [KeysNodup, GenG37.mem0],
      fun b al a h => by simp [GenG37.mem0] at h⟩
    rw [s0_regs hv]
    trivial
  slots := by intro k v h; simp [s0] at h

/-- **G43 on `runtime.(*debugLogWriter).varint`**: `InitMem` (`v1`) sits in the return block `b2`
before the call `v24`, so not all values keep the memory (`memPure` fails) and `checkG42` rejects
the function; `b2` is a clean block (no value that changes the memory precedes it on a path from
the entry, `cleanOK`), `(b2, 1)` is clean, and `checkG43` accepts it. From the state before `v1`,
which holds the activation's initial memory, `stepLoc` runs `v1` to a state that holds it again at
the clean position `(b2, 2)` (`memInit_clean_step`), and `g43_initMem` relates it to the machine
after no code, under an activation extending `E` that is again a `G28Env`. -/
theorem genG43_witness :
    (checkG42 lc0 ps bs g).toOption = none ∧ memPure lc = false ∧
      cleanOK lc (cleanBlocks lc) = true ∧ cleanAt lc (cleanBlocks lc) 2 blk 1 = true ∧
      MemInit s0 ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 1) = .ok s1 ∧
        cleanAt lc (cleanBlocks lc) 2 blk 2 = true ∧ MemInit s1 ∧
        E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 2 2 m1 := by
  obtain ⟨hl, hc, h42, hp, hok, hc1, hc2, hav, hsl, hm1, hb, hv1, hi1, hop, hrun⟩ := facts
  obtain ⟨s1, hs1, -⟩ := GenG1.okThen_spec hrun
  have hE := g43Env hc hl hav hsl
  have hM0 : MemInit s0 := rfl
  -- `g43_initMem` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 2 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 2 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 1 = some (val 1) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv1
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g43_initMem (H := GenG2.H0) (env := GenG2.env)
    hc hE hl0 hm0 hb0 hi1 hv0 hop locMatch0 g43Inv0 hM0 hs1
  exact ⟨h42, hp, hok, hc1, hM0, s1, E1, m1, hs1, hc2,
    memInit_clean_step hl hi1 hv1 (fun _ => hM0) hs1 hc2, hx1, hE1, hp1, hm1'⟩

end GoFV.Proof.Witness.GenG43
