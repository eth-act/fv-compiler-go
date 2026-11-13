import GoFV.Proof.Gen.G58
import GoFV.Proof.Witness.GenG58

/-!
# Witness: slice G59 group U (G35's upper-bit table across a shifted logic op) on
`runtime.(*scavChunkData).pack`

`std/std/runtime/(*scavChunkData).pack` (quick-v10), loaded as `gen-check` does (`GenG2.load` of
its embedded `.ssa`/`.prog`). In its block `b4`, `v24 = LDPW` loads two words into `R1`, `R2`
(G35's table: `R1`, `R2` zero-extended 32-bit words), `v3 = MOVBU` a byte into `R3`, and
`v29 = ORshiftLL v25 v26` (`ORR R3<<26, R1, R1`) writes only `R1`; `v31 = MOVDnop v5` then needs
`R2`'s entry. Before group U, G35's table took G34's step across `ORshiftLL`, which empties it
(`uStep34 … = []`), so `checkG58` rejected the function (`MOVDnop/MOVDreg: upper bits unknown`);
with `pairOp35` covering G27's shifted logic ops the table keeps `R3`'s and `R2`'s entries and
`checkG58` accepts it with the PC table `tab59` and the class table `kt59`. From a state `s0` with
`R1 = 5`, `R2 = 7`, `R3 = 3`, `g58_value` relates `v29`'s run to the machine's `ORR`, after which
the table's entry for `R2` holds: `X2` is still a zero-extended 32-bit word.
-/

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG59u

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/(*scavChunkData).pack,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "(*scavChunkData).pack" 1 0 0
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
type t4 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t5 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t6 UINT8 1 1 0 comparable,named "scavChunkFlags" "runtime.scavChunkFlags"
type t3 STRUCT 12 4 0 comparable,named "scavChunkData" "runtime.scavChunkData" 4
field 0 "inUse" t4 0 0
field 1 "lastInUse" t4 2 0
field 2 "gen" t5 4 0
field 3 "scavChunkFlags" t6 8 1
type t2 PTR 8 8 8 hasptr,direct,comparable "*scavChunkData" "*runtime.scavChunkData" t3
type t7 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t1 FUNC 8 8 8 hasptr,direct "method(*scavChunkData) func() uint64" "method(*runtime.scavChunkData) func() uint64" 1 0 1
field 0 "sc" t2 ? 0
field 1 "" t7 ? 0
aux a2 sym "runtime.(*scavChunkData).pack" "runtime.(*scavChunkData).pack" 1 - 0 - - - - 0
posbase p57 "runtime/mgcscavenge.go" 1 1 -1
aux a3 name "sc" "sc" PPARAM t2 0 1 used p57:1248:7:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t7 0 1 - p57:1248:32:0:0
aux a1 call "AuxCall{runtime.(*scavChunkData).pack}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t7 a4 0 -1
type t8 BOOL 1 1 0 comparable,named "bool" "bool"
type t9 INT8 1 1 0 comparable,named "int8" "int8"
type t10 INT16 2 2 0 comparable,named "int16" "int16"
type t11 INT32 4 4 0 comparable,named "int32" "int32"
type t12 INT64 8 8 0 comparable,named "int64" "int64"
type t13 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t14 INT 8 8 0 comparable,named "int" "int"
type t15 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t16 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t17 UINT 8 8 0 comparable,named "uint" "uint"
type t18 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t19 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t13
type t21 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t11
type t22 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t5
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
posbase p1 "<autogenerated>" 1 1 -1
type t36 PTR 8 8 8 hasptr,direct,comparable "**scavChunkData" "**runtime.scavChunkData" t2
type t37 PTR 8 8 8 hasptr,direct,comparable "*uint64" "*uint64" t7
posbase p10226 "runtime/mgcscavenge.go" 1 1 9947
aux a6 sym "runtime.panicwrap" "runtime.panicwrap" 1 - 0 - - - - 0
aux a5 call "AuxCall{runtime.panicwrap}" a6 1 0 0 8 0 0 0
type t38 RESULTS ? ? ? - "uint64,mem" "" 2 t7,t31
slot s1 a3 t2 0 - 0
aux a7 name "sc" "sc" PAUTO t3 0 1 used p10226:1248:7:0:0
slot s2 a7 t3 0 - 0
aux a8 name "~r0" "~r0" PAUTO t7 0 1 - p10226:1248:32:0:0
slot s3 a8 t7 0 - 0
f b1 t1 a1 37 4
typs Bool=t8,Int8=t9,Int16=t10,Int32=t11,Int64=t12,UInt8=t13,UInt16=t4,UInt32=t5,UInt64=t7,Int=t14,Float32=t15,Float64=t16,UInt=t17,Uintptr=t18,String=t19,BytePtr=t20,Int32Ptr=t21,UInt32Ptr=t22,IntPtr=t23,UintptrPtr=t24,Float32Ptr=t25,Float64Ptr=t26,BytePtrPtr=t27,Complex64=t28,Complex128=t29,UnsafePtr=t30,Mem=t31,Flags=t32,Void=t33,Int128=t34,ResultMem=t35
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t37 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 Const64 t7 0 - p0:0:0:0:0 0 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t8 0 - p1:1:0:0:0 1 v6,v8
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:0 b1:1
v v13 Copy t2 0 - p1:1:0:2:0 1 v6
v v14 Copy t31 0 - p1:1:0:2:0 4 v1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v13,v14
v v16 Load t3 0 - p1:1:0:0:0 4 v15,v14
v v17 InlMark t33 9947 - p1:1:0:1:0 0 v14
v v18 StructSelect t4 0 - p10226:1249:18:0:0 1 v16
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:0:0 1 v18
v v20 StructSelect t4 1 - p10226:1250:13:0:0 1 v16
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:0:0 1 v20
v v23 Lsh64x64 t7 0 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:0:0 1 v19,v23
v v25 StructSelect t6 3 - p10226:1251:13:0:0 1 v16
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:0:0 1 v25
v v28 Lsh64x64 t7 0 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:0:0 1 v24,v28
v v30 StructSelect t5 2 - p10226:1252:13:0:0 1 v16
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:0:0 1 v30
v v33 Lsh64x64 t7 0 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:0:0 1 v29,v33
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v10 Copy t31 0 - p1:1:0:2:0 1 v1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v10
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b2:0
v v35 Copy t7 0 - p1:1:0:2:0 1 v34
v v36 Copy t31 0 - p1:1:0:2:0 1 v14
v v37 MakeResult t38 0 - p1:1:0:0:0 1 v35,v36
names s1,s2,s3
named s1 v6,v13
named s2 v16
named s3 v34,v35
splits -
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 0=v7,16=v22,26=v27,32=v32,3344556677=v8
freev -
freeb -
dcllen 4
end
pass 1 "number lines"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t37 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 Const64 t7 0 - p0:0:0:0:0 0 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t8 0 - p1:1:0:1:0 1 v6,v8
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:0 b1:1
v v13 Copy t2 0 - p1:1:0:2:0 1 v6
v v14 Copy t31 0 - p1:1:0:2:0 4 v1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v13,v14
v v16 Load t3 0 - p1:1:0:0:0 4 v15,v14
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v14
v v18 StructSelect t4 0 - p10226:1249:18:0:0 1 v16
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v18
v v20 StructSelect t4 1 - p10226:1250:13:0:0 1 v16
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v20
v v23 Lsh64x64 t7 0 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v19,v23
v v25 StructSelect t6 3 - p10226:1251:13:0:0 1 v16
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v25
v v28 Lsh64x64 t7 0 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v24,v28
v v30 StructSelect t5 2 - p10226:1252:13:0:0 1 v16
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v30
v v33 Lsh64x64 t7 0 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v29,v33
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v10 Copy t31 0 - p1:1:0:2:0 1 v1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v10
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b2:0
v v35 Copy t7 0 - p1:1:0:2:0 1 v34
v v36 Copy t31 0 - p1:1:0:2:0 1 v14
v v37 MakeResult t38 0 - p1:1:0:0:0 1 v35,v36
names s1,s2,s3
named s1 v6,v13
named s2 v16
named s3 v34,v35
splits -
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 0=v7,16=v22,26=v27,32=v32,3344556677=v8
freev -
freeb -
cache postorder b3,b4,b2,b1
cache linestarts 1:1:1,10226:1249:1252
dcllen 4
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 10 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t37 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 3 -
v v7 Const64 t7 0 - p0:0:0:0:0 0 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t8 0 - p1:1:0:1:0 1 v6,v8
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:0 b1:1
v v13 Copy t2 0 - p1:1:0:2:0 0 v6
v v14 Copy t31 0 - p1:1:0:2:0 0 v1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 4 v15,v1
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v18 StructSelect t4 0 - p10226:1249:18:0:0 1 v16
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v18
v v20 StructSelect t4 1 - p10226:1250:13:0:0 1 v16
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v20
v v23 Lsh64x64 t7 0 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v19,v23
v v25 StructSelect t6 3 - p10226:1251:13:0:0 1 v16
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v25
v v28 Lsh64x64 t7 0 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v24,v28
v v30 StructSelect t5 2 - p10226:1252:13:0:0 1 v16
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v30
v v33 Lsh64x64 t7 0 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 2 v29,v33
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v10 Copy t31 0 - p1:1:0:2:0 0 v1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b2:0
v v35 Copy t7 0 - p1:1:0:2:0 0 v34
v v36 Copy t31 0 - p1:1:0:2:0 0 v1
v v37 MakeResult t38 0 - p1:1:0:0:0 1 v34,v1
names s1,s2,s3
named s1 v6,v6
named s2 v16
named s3 v34,v34
splits -
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 0=v7,16=v22,26=v27,32=v32,3344556677=v8
freev -
freeb -
cache postorder b3,b4,b2,b1
cache linestarts 1:1:1,10226:1249:1252
dcllen 4
end
pass 3 "early deadcode"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t8 0 - p1:1:0:1:0 1 v6,v8
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:0 b1:1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 4 v15,v1
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v18 StructSelect t4 0 - p10226:1249:18:0:0 1 v16
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v18
v v20 StructSelect t4 1 - p10226:1250:13:0:0 1 v16
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v20
v v23 Lsh64x64 t7 0 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v19,v23
v v25 StructSelect t6 3 - p10226:1251:13:0:0 1 v16
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v25
v v28 Lsh64x64 t7 0 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v24,v28
v v30 StructSelect t5 2 - p10226:1252:13:0:0 1 v16
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v30
v v33 Lsh64x64 t7 0 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v29,v33
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b2:0
v v37 MakeResult t38 0 - p1:1:0:0:0 1 v34,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v34
splits -
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32,3344556677=v8
freev v36,v35,v10,v14,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b4,b2,b1
cache linestarts 1:1:1,10226:1249:1252
dcllen 4
end
pass 4 "short circuit"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b4:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t8 0 - p1:1:0:1:0 1 v6,v8
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 BlockInvalid p1:1:0:1:0 0 0 - - - -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 4 v15,v1
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v18 StructSelect t4 0 - p10226:1249:18:0:0 1 v16
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v18
v v20 StructSelect t4 1 - p10226:1250:13:0:0 1 v16
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v20
v v23 Lsh64x64 t7 0 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v19,v23
v v25 StructSelect t6 3 - p10226:1251:13:0:0 1 v16
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v25
v v28 Lsh64x64 t7 0 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v24,v28
v v30 StructSelect t5 2 - p10226:1252:13:0:0 1 v16
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v30
v v33 Lsh64x64 t7 0 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v29,v33
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v34
splits -
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32,3344556677=v8
freev v36,v35,v10,v14,v13,v7,v5,v4,v3,v2
freeb -
cache linestarts 1:1:1,10226:1249:1252
dcllen 4
end
pass 5 "decompose user"
aux a9 name "scinUse" "scinUse" PAUTO t4 0 3 used p10226:1248:7:0:0
slot s4 a9 t4 0 s2 0
aux a10 name "sclastInUse" "sclastInUse" PAUTO t4 0 3 used p10226:1248:7:0:0
slot s5 a10 t4 0 s2 2
aux a11 name "scgen" "scgen" PAUTO t5 0 3 used p10226:1248:7:0:0
slot s6 a11 t5 0 s2 4
aux a12 name "scscavChunkFlags" "scscavChunkFlags" PAUTO t6 0 3 used p10226:1248:7:0:0
slot s7 a12 t6 0 s2 8
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b4:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t8 0 - p1:1:0:1:0 1 v6,v8
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 BlockInvalid p1:1:0:1:0 0 0 - - - -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 4 v15,v1
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v18 StructSelect t4 0 - p10226:1249:18:0:0 1 v16
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v18
v v20 StructSelect t4 1 - p10226:1250:13:0:0 1 v16
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v20
v v23 Lsh64x64 t7 0 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v19,v23
v v25 StructSelect t6 3 - p10226:1251:13:0:0 1 v16
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v25
v v28 Lsh64x64 t7 0 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v24,v28
v v30 StructSelect t5 2 - p10226:1252:13:0:0 1 v16
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v30
v v33 Lsh64x64 t7 0 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v29,v33
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3,s4,s5,s6,s7
named s1 v6
named s3 v34
named s4 -
named s5 -
named s6 -
named s7 -
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32,3344556677=v8
freev v36,v35,v10,v14,v13,v7,v5,v4,v3,v2
freeb -
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b4:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t8 0 - p1:1:0:1:0 1 v6,v8
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 4 v15,v1
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v18 StructSelect t4 0 - p10226:1249:18:0:0 1 v16
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v18
v v20 StructSelect t4 1 - p10226:1250:13:0:0 1 v16
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v20
v v23 Lsh64x64 t7 0 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v19,v23
v v25 StructSelect t6 3 - p10226:1251:13:0:0 1 v16
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v25
v v28 Lsh64x64 t7 0 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v24,v28
v v30 StructSelect t5 2 - p10226:1252:13:0:0 1 v16
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v30
v v33 Lsh64x64 t7 0 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v29,v33
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32,3344556677=v8
freev v36,v35,v10,v14,v13,v7,v5,v4,v3,v2
freeb b2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 7 "opt"
type t39 PTR 8 8 8 hasptr,direct,comparable "*uint16" "*uint16" t4
type t40 PTR 8 8 8 hasptr,direct,comparable "*scavChunkFlags" "*runtime.scavChunkFlags" t6
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 4 v6,v1
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v19,v23
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v24,v28
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v29,v33
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v15
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v15
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v15
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v15
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 8 "zero arg cse"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 4 v6,v1
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v19,v23
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v24,v28
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v29,v33
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v15
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v15
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v15
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v15
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 9 "opt deadcode"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 4 v6,v1
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v19,v23
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v24,v28
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v29,v33
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v15
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v15
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v15
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v15
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 10 "generic cse"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 4 v6,v1
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v15
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v15
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v15
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v15
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 11 "phiopt"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 4 v6,v1
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v15
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v15
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v15
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v15
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 12 "gcse deadcode"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 4 v6,v1
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v15
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v15
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v15
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v15
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 13 "nilcheckelim"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v15 Copy t2 0 - p1:1:0:0:0 4 v6
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v15
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v15
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v15
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v15
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 14 "prove"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v15 Copy t2 0 - p1:1:0:0:0 4 v6
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v15
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v15
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v15
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v15
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 15 "divisible"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 Arg t2 0 a3 p1:1:0:2:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v15,v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 16 "divmod"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 Arg t2 0 a3 p1:1:0:2:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v15,v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 17 "middle opt"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 Arg t2 0 a3 p1:1:0:2:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v15,v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 18 "known bits"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 Arg t2 0 a3 p1:1:0:2:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v15,v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 19 "early fuse"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 Arg t2 0 a3 p1:1:0:2:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v15,v30,v25,v20,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 20 "expand calls"
aux a13 nameoff "sc+0" a3 0
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
v v15 SB t18 0 - p0:0:0:0:0 0 -
v v30 SP t18 0 - p0:0:0:0:0 2 -
v v25 OffPtr t36 0 - p0:0:0:0:0 0 v30
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 LocalAddr t37 0 a4 p1:1:0:1:0 0 v30,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 0=v25,16=v22,26=v27,32=v32
freev v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 21 "decompose builtin"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
v v15 SB t18 0 - p0:0:0:0:0 0 -
v v30 SP t18 0 - p0:0:0:0:0 2 -
v v25 OffPtr t36 0 - p0:0:0:0:0 0 v30
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 LocalAddr t37 0 a4 p1:1:0:1:0 0 v30,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 0=v25,16=v22,26=v27,32=v32
freev v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 22 "softfloat"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
v v15 SB t18 0 - p0:0:0:0:0 0 -
v v30 SP t18 0 - p0:0:0:0:0 2 -
v v25 OffPtr t36 0 - p0:0:0:0:0 0 v30
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 LocalAddr t37 0 a4 p1:1:0:1:0 0 v30,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 0=v25,16=v22,26=v27,32=v32
freev v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 23 "branchelim"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
v v15 SB t18 0 - p0:0:0:0:0 0 -
v v30 SP t18 0 - p0:0:0:0:0 2 -
v v25 OffPtr t36 0 - p0:0:0:0:0 0 v30
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 LocalAddr t37 0 a4 p1:1:0:1:0 0 v30,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 0=v25,16=v22,26=v27,32=v32
freev v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 24 "late opt"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v20,v25,v30,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 25 "dead auto elim"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v20,v25,v30,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 26 "sccp"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v20,v25,v30,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 27 "generic deadcode"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v20,v25,v30,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 28 "late fuse"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v20,v25,v30,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 29 "check bce"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v20,v25,v30,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 30 "dse"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 1 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 Load t4 0 - p1:1:0:0:0 1 v35,v1
v v13 Load t4 0 - p1:1:0:0:0 1 v14,v1
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 1 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 1 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Or64 t7 0 - p10226:1249:26:1:0 1 v23,v19
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v20,v25,v30,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 31 "memcombine"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 0 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 OpInvalid t4 0 - p1:1:0:0:0 1 -
v v13 OpInvalid t4 0 - p1:1:0:0:0 1 -
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 0 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 0 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Copy t7 0 - p10226:1249:26:1:0 1 v25
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Load t5 0 - p1:1:0:0:0 1 v35,v1
v v25 ZeroExt32to64 t7 0 - p1:1:0:0:0 1 v20
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v30,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 32 "writebarrier"
f b1 t1 a1 37 4
b b1 If p1:1:0:0:0 0 0 - v36 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 5 -
v v22 Const64 t17 16 - p0:0:0:0:0 1 -
v v27 Const64 t17 26 - p0:0:0:0:0 1 -
v v32 Const64 t17 32 - p0:0:0:0:0 1 -
v v36 IsNonNil t8 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v4 OffPtr t40 8 - p1:1:0:0:0 1 v6
v v7 OffPtr t22 4 - p1:1:0:0:0 1 v6
v v14 OffPtr t39 2 - p1:1:0:0:0 0 v6
v v35 OffPtr t39 0 - p1:1:0:0:0 1 v6
v v3 Load t6 0 - p1:1:0:0:0 1 v4,v1
v v5 Load t5 0 - p1:1:0:0:0 1 v7,v1
v v10 OpInvalid t4 0 - p1:1:0:0:0 1 -
v v13 OpInvalid t4 0 - p1:1:0:0:0 1 -
v v19 ZeroExt16to64 t7 0 - p10226:1249:18:1:0 0 v10
v v21 ZeroExt16to64 t7 0 - p10226:1250:13:1:0 1 v13
v v26 ZeroExt8to64 t7 0 - p10226:1251:13:1:0 1 v3
v v31 ZeroExt32to64 t7 0 - p10226:1252:13:1:0 1 v5
v v23 Lsh64x64 t7 1 - p10226:1250:25:0:0 0 v21,v22
v v28 Lsh64x64 t7 1 - p10226:1251:30:0:0 1 v26,v27
v v33 Lsh64x64 t7 1 - p10226:1252:19:0:0 1 v31,v32
v v24 Copy t7 0 - p10226:1249:26:1:0 1 v25
v v29 Or64 t7 0 - p10226:1250:32:1:0 1 v28,v24
v v34 Or64 t7 0 - p10226:1251:62:1:0 1 v33,v29
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Load t5 0 - p1:1:0:0:0 1 v35,v1
v v25 ZeroExt32to64 t7 0 - p1:1:0:0:0 1 v20
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts 16=v22,26=v27,32=v32
freev v30,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 33 "lower"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 4 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 ARM64MOVWUload t5 4 - p1:1:0:0:0 1 v6,v1
v v26 ARM64MOVBUreg t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVWUreg t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 ARM64MOVWUload t5 0 - p1:1:0:0:0 1 v6,v1
v v25 ARM64MOVWUreg t7 0 - p1:1:0:0:0 1 v20
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v24,v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252:1249=4
dcllen 8
end
pass 34 "addressing modes"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 4 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 ARM64MOVWUload t5 4 - p1:1:0:0:0 1 v6,v1
v v26 ARM64MOVBUreg t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVWUreg t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 ARM64MOVWUload t5 0 - p1:1:0:0:0 1 v6,v1
v v25 ARM64MOVWUreg t7 0 - p1:1:0:0:0 1 v20
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v24,v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252:1249=4
dcllen 8
end
pass 35 "late lower"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 4 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 ARM64MOVWUload t5 4 - p1:1:0:0:0 1 v6,v1
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 ARM64MOVWUload t5 0 - p1:1:0:0:0 1 v6,v1
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v24,v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 36 "pair"
type t41 TUPLE ? ? ? - "uint32,uint32" "" t5 t5
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 38 "lowered cse"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 39 "elim unread autos"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 41 "lowered deadcode"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 42 "checkLower"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 43 "loop invariant"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 45 "tighten"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 46 "late deadcode"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 47 "critical"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 48 "phi tighten"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 49 "likelyadjust"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b4:5:8,b4:b1:-:-:11:14
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
dcllen 8
end
pass 50 "layout"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b4:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b4:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b4:b1:-:-:11:14,b3:b1:-:b4:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
fstate laidout
dcllen 8
end
pass 51 "schedule"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b4:0,b3:0 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b4:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b4:b1:-:-:11:14,b3:b1:-:b4:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
fstate scheduled,laidout
dcllen 8
end
pass 52 "late nilcheck"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b4:0,b3:0 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b4:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b4:b1:-:-:11:14,b3:b1:-:b4:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
fstate scheduled,laidout
dcllen 8
end
pass 53 "flagalloc"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b4:0,b3:0 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v33,v28,v23,v21,v19,v13,v10,v35,v14,v7,v4,v30,v36,v32,v27,v22,v15,v18,v16,v9,v8,v2
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b4:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b4:b1:-:-:11:14,b3:b1:-:b4:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
fstate scheduled,laidout
dcllen 8
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.(*scavChunkData).pack}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t7 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b4:0,b3:0 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v2,v4,v7,v8,v9,v10,v13,v14,v15,v16,v18,v19,v21,v22,v23,v27,v28,v30,v32,v33,v35,v36
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b4:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b4:b1:-:-:11:14,b3:b1:-:b4:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
fstate scheduled,laidout
regalloc 38 v3:R3,v5:R2,v6:R0,v20:R1,v24:(R1;R2),v25:R1,v26:R3,v29:R1,v31:R2,v34:R0,v37:[]
dcllen 8
end
pass 55 "loop rotate"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b4:0,b3:0 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v2,v4,v7,v8,v9,v10,v13,v14,v15,v16,v18,v19,v21,v22,v23,v27,v28,v30,v32,v33,v35,v36
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b4:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b4:b1:-:-:11:14,b3:b1:-:b4:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
fstate scheduled,laidout
regalloc 38 v3:R3,v5:R2,v6:R0,v20:R1,v24:(R1;R2),v25:R1,v26:R3,v29:R1,v31:R2,v34:R0,v37:[]
dcllen 8
end
pass 56 "trim"
f b1 t1 a1 37 4
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b4:0,b3:0 -
v v6 ArgIntReg t2 0 a13 p1:1:0:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
b b4 Ret p1:1:0:1:0 0 0 - v37 - b1:0
v v24 ARM64LDPW t41 0 - p1:1:0:0:0 2 v6,v1
v v5 Select1 t5 0 - p1:1:0:0:0 1 v24
v v20 Select0 t5 0 - p1:1:0:0:0 1 v24
v v3 ARM64MOVBUload t6 8 - p1:1:0:0:0 1 v6,v1
v v25 ARM64MOVDnop t7 0 - p1:1:0:0:0 1 v20
v v26 ARM64MOVDnop t7 0 - p10226:1251:13:1:0 1 v3
v v29 ARM64ORshiftLL t7 26 - p10226:1250:32:1:0 1 v25,v26
v v31 ARM64MOVDnop t7 0 - p10226:1252:13:1:0 1 v5
v v34 ARM64ORshiftLL t7 32 - p10226:1251:62:1:0 1 v29,v31
v v17 InlMark t33 9947 - p1:1:0:0:0 0 v1
v v37 MakeResult t38 0 - p1:1:0:1:0 1 v34,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t35 0 a5 p1:1:0:0:0 1 v1
v v12 SelectN t31 0 - p1:1:0:0:0 1 v11
names s1,s3
named s1 v6
named s3 v34
namedx a7/t3/0/-/0 v16
splits s2/0/t4=s4,s2/2/t4=s5,s2/4/t5=s6,s2/8/t6=s7
canon a3/t2/0/-/0=s1,a7/t3/0/-/0=s2,a8/t7/0/-/0=s3
consts -
freev v2,v4,v7,v8,v9,v10,v13,v14,v15,v16,v18,v19,v21,v22,v23,v27,v28,v30,v32,v33,v35,v36
freeb b2
cache postorder b4,b3,b1
cache idom b1:-,b4:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b4:b1:-:-:11:14,b3:b1:-:b4:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a13:3
cache linestarts 1:1:1,10226:1249:1252
fstate scheduled,laidout
regalloc 38 v3:R3,v5:R2,v6:R0,v20:R1,v24:(R1;R2),v25:R1,v26:R3,v29:R1,v31:R2,v34:R0,v37:[]
dcllen 8
end
frontend
end
ptrcache t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t24,t27,t28,t29,t30
typelink t31=t35
typeorder t9,t13,t6,t10,t4,t11,t5,t12,t7,t14,t17,t18,t28,t29,t15,t16,t8,t20,t40,t39,t21,t22,t37,t23,t24,t25,t26,t27,t36,t2,t1,t3,t19,t30,t31,t33,t32,t34,t41,t35,t38
eof
"#

/-- `std/std/runtime/(*scavChunkData).pack,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "(*scavChunkData).pack" 1
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
type t1 8 8 8 1 01 "*scavChunkData"
name n1 "sc" PPARAM t1 1 "runtime.sc" 0 a3
type t2 8 8 0 0 - "uint64"
name n2 "~r0" PPARAMOUT t2 1 "runtime.~r0" 0 a4
type t3 12 4 0 0 - "scavChunkData"
name n3 "sc" PAUTO t3 1 "runtime.sc" 0 a7
name n4 "~r0" PAUTO t2 1 "runtime.~r0" 0 a8
type t4 2 2 0 0 - "uint16"
name n5 "scinUse" PAUTO t4 3 "runtime.scinUse" 0 a9
name n6 "sclastInUse" PAUTO t4 3 "runtime.sclastInUse" 0 a10
type t5 4 4 0 0 - "uint32"
name n7 "scgen" PAUTO t5 3 "runtime.scgen" 0 a11
type t6 1 1 0 0 - "scavChunkFlags"
name n8 "scscavChunkFlags" PAUTO t6 3 "runtime.scscavChunkFlags" 0 a12
in n1 0 used
in n2 0 outregs
in n3 0 used
in n4 0 -
in n5 0 used
in n6 0 used
in n7 0 used
in n8 0 used
out n1 0 used
opt n2 0 outregs
opt n4 0 -
opt n3 0 -
opt n7 0 -
opt n5 0 -
opt n6 0 -
opt n8 0 -
stack 0 0 8
end
genin
posbase p1 "<autogenerated>" 1 1 -1 0 "<autogenerated>" "<autogenerated>" 1 1
sym y1 "runtime.(*scavChunkData).pack" 1
curfn p1:1:0:0:0 0 0
regargs 8192:0:t1
text y1 0 0 23 0 1 200091
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.(*scavChunkData).pack.arginfo1" 0
sym y5 "runtime.(*scavChunkData).pack.argliveinfo" 0
sym y6 "runtime.scavChunkData.pack" 1
inl i9947 - p1:1:0:0:0 y6 "scavChunkData.pack"
posbase p10226 "runtime/mgcscavenge.go" 1 1 9947 56 "runtime/mgcscavenge.go" "runtime/mgcscavenge.go" 1 1
sym y7 "runtime.panicwrap" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p1:1:0:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p1:1:0:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p1:1:0:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p1:1:0:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p1:1:0:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p1:1:0:1:0
p 7 7 0 0 0 - CBZ 0 REG/8192/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@14 0 0 p1:1:0:1:0
p 8 8 0 0 0 - LDPW 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REGREG/8193/0/0/NONE/0/8194/-/- 0 0 p1:1:0:2:0
p 9 9 0 0 0 - MOVBU 0 MEM/8192/0/0/NONE/0/8/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p1:1:0:2:0
p 10 10 0 0 0 - ORR 0 SHIFT/0/0/0/NONE/0/223232/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p10226:1250:32:1:0
p 11 11 0 0 0 - ORR 0 SHIFT/0/0/0/NONE/0/163840/-/- 8193 - REG/8192/0/0/NONE/0/0/-/- 0 0 p10226:1251:62:1:0
p 12 12 0 0 0 - NOP 0 _ 0 - _ 0 0 p0:0:0:0:0
p 13 13 0 0 0 - RET 0 _ 0 - _ 0 0 p1:1:0:1:0
p 14 14 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p1:1:0:2:0
p 15 15 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p1:1:0:2:0
p 16 16 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p1:1:0:0:0
p 17 17 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 23 0 1 200091
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
inlmark @7 9947
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgslot 1 n4 t2 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:4:34:50
dbgregout n2
dbgpc 4:34:12
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p1:1:0:0:0
p 18 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 19 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:0:0
p 20 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:0:0
p 21 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@30 0 0 p1:1:0:0:0
p 22 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p1:1:0:0:0
p 23 12 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p1:1:0:0:1
p 24 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p1:1:0:0:0
p 25 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p1:1:0:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p1:1:0:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p1:1:0:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p1:1:0:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p1:1:0:2:0
p 6 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:1:0
p 7 24 0 0 85 - CBZ 0 REG/8192/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/14/-/@14 0 0 p1:1:0:1:0
p 8 28 0 0 262 - LDPW 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REGREG/8193/0/0/NONE/7/8194/-/- 0 0 p1:1:0:2:0
p 9 32 0 0 294 - MOVBU 0 MEM/8192/0/0/NONE/87/8/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p1:1:0:2:0
p 10 36 0 0 51 - ORR 0 SHIFT/0/0/0/NONE/8/223232/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p10226:1250:32:1:0
p 11 40 0 0 51 - ORR 0 SHIFT/0/0/0/NONE/8/163840/-/- 8193 - REG/8192/0/0/NONE/2/0/-/- 0 0 p10226:1251:62:1:0
p 12 44 0 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p0:0:0:0:0
p 13 44 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 26 48 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 27 52 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p1:1:0:1:0
p 14 56 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p1:1:0:2:0
p 15 56 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y7/- 0 0 p1:1:0:2:0
p 16 60 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:0:0
p 28 64 -16 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:0:0
p 29 64 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p1:1:0:0:0
p 30 64 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:0:0
p 31 64 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p1:1:0:0:0
p 32 68 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 33 72 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y8/- 0 0 p1:1:0:0:0
p 34 76 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p1:1:0:0:0
p 35 76 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 36 80 16 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@18 0 0 p1:1:0:0:0
fn y1 8 8 23 0 1 200091
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
inlmark @7 9947
funcaux y2 y3 - - y4 y5 -
text 96 0 900b40f9ff6330ebc9010054fe0f1ff8fd831ff8fd2300d1000100b40108402903204039216803aa208002aafd835ff8fe0741f8c0035fd6000000941f2003d5e00700f9e3031eaa00000094e00740f9ecffff17000000000000000000000000 2
reloc 56 4 R_CALLARM64 0 y7
reloc 72 4 R_CALLARM64 0 y8
pcln y13 y14 y15 y16 y9,y10,y11,y12 y2,y3,_,_,_,y4,y5
usedfiles 0,56
inltree 0 -1 p1:1:0:0:0 y6 "scavChunkData.pack" 24
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y9 SRODATA 11 1 28000 000101020203010d020500 0
data y10 SRODATA 7 1 28000 000e0402030800 0
data y11 SRODATA 0 1 28000 - 0
data y12 SRODATA 5 1 28000 0006041200 0
data y13 SRODATA 11 1 28000 020420091f0120021f0800 0
data y14 SRODATA 7 1 28000 020970026f0d00 0
data y15 SRODATA 11 1 28000 0409c213010201c3130d00 0
data y16 SRODATA 7 1 28000 00090202010d00 0
end
dwarf
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
posbase p57 "runtime/mgcscavenge.go" 1 1 -1 56 "runtime/mgcscavenge.go" "runtime/mgcscavenge.go" 1 1
sym y21 "go:info.runtime.scavChunkData.pack$abstract" 0
sym y22 "go:info.*runtime.scavChunkData" 0
sym y23 "go:info.uint64" 0
sym y24 "type:uint64" 0
dwfn y17 y18 y19 - y20 "runtime.(*scavChunkData).pack" 0:1 1 1 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwinlfn y6 y21
dwinldcl y6 "sc" 0 p57:1248:7:0:0
dwinldcl y6 "~r0" 0 p57:1248:32:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime.scavChunkData" 0 0 1 p57:1248:7:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uint64" 0 0 1 p57:1248:32:0:0
dwname n4 1 0 0 1 0 0 0 0 - - "uint64" 0 0 1 p10226:1248:32:0:0
dwname n3 1 0 0 1 0 0 0 0 - - "runtime.scavChunkData" 0 0 1 p10226:1248:7:0:0
dwname n7 1 0 0 0 0 0 0 0 - - "uint32" 0 0 1 p10226:1248:7:0:0
dwname n5 1 0 0 0 0 0 0 0 - - "uint16" 0 0 1 p10226:1248:7:0:0
dwname n6 1 0 0 0 0 0 0 0 - - "uint16" 0 0 1 p10226:1248:7:0:0
dwname n8 1 0 0 0 0 0 0 0 - - "runtime.scavChunkFlags" 0 0 1 p10226:1248:7:0:0
var 0 0 "sc" 5 1 0 0 0 8 y22 "runtime/mgcscavenge.go" 1248 7 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y23 "runtime/mgcscavenge.go" 1248 32 0 1 0 0 -
scope 0 0 - 0,1
inlcall 0 9947 0:1 y21 - 1 36:44 -
data y17 SDWARFFCN 81 0 0 0472756e74696d652e282a736361764368756e6b44617461292e7061636b00000060019c012d73630000e00900000000000000002e7e72300001e009000000000009000000000000000001000000010000 7
reloc 0 0 R_USETYPE 0 y24
reloc 31 2 R_DWTXTADDR_U2 0 y1
reloc 44 4 R_DWARFSECREF 0 y22
reloc 48 4 R_DWARFSECREF 0 y18
reloc 60 4 R_DWARFSECREF 0 y23
reloc 66 4 R_DWARFSECREF 0 y21
reloc 70 4 R_DWARFSECREF 0 y19
data y18 SDWARFLOC 9 0 0 01000004002c015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y19 SDWARFRANGE 7 0 0 01000004242c00 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y20 SDWARFLINES 38 0 0 00090200000000000000000a8706af04390603dc096438040103a27633068706370224000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `runtime.(*scavChunkData).pack`. -/
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

def blk : Block := (lc.ctx.f.block? 4).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- The PC table `checkG58` computes: `b4`'s `v29` (index 6) starts at Prog 10, its `ORR`. -/
def tab59 : PcTab :=
  [(1, [5, 5, 5]), (4, [8, 9, 9, 9, 10, 10, 10, 11, 11, 12, 12, 12]), (3, [14, 16, 16])]

/-- The class table `checkG58` computes. -/
def kt59 : KTab :=
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)

/-- P0's layout: `GenG58a`'s, a 16-byte frame with 8 bytes of extra space. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation whose `outargs` block sits at `SP` (`GenG48.ι48`, `SP = GenG48.spO`,
`g = 0x9000`, saved `LR` and `FP` 0) with the globals at `symA`, no home slot, the PC table
`tab59`. -/
def E59 : MatchEnv :=
  { lc, ι := GenG48.ι48, sp := GenG48.spO, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab59, outSP := true }

/-- The `runLoc` state before `v29`: `R1 = 5` (`v25`), `R2 = 7` (`v5`, a 32-bit word),
`R3 = 3` (`v26`), every other register `poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 1 then .int .w64 5 else if i.val = 2 then .int .w32 7
      else if i.val = 3 then .int .w64 3 else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v29`: the registers' words, the activation's `g` and `FP`, the PC of
`v29`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 1 then 5 else if k = 2 then 7 else if k = 3 then 3
      else if k = 28 then 0x9000 else if k = 29 then GenG48.spO - 8 else 0,
    sp := GenG48.spO, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E59.pcOf 4 6, mem := fun _ => 0 }

/-- The register value `.int .w64 0xC000005` (`5 ||| 3 <<< 26`). -/
def isRes : Option Val → Bool
  | some (.int .w64 x) => x == 0xC000005
  | _ => false

theorem isRes_spec {o : Option Val} (h : isRes o = true) : o = some (.int .w64 0xC000005) := by
  unfold isRes at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- What compiled evaluation checks on `runtime.(*scavChunkData).pack`: `checkG58` accepts it with
`tab59` and `kt59`; the Progs have IDs below `2^32`; no frame variable is accessed and there is no
home slot; `b4` is a block holding `v29 = ORshiftLL` at index 6; the class table before `v29` holds
`R1`, `R3` at 64 and `R2` at 32 bits; G35's table before `v29` holds `R3`, `R1`, `R2` and after it
`R3`, `R2`, while G34's step (G35's across `ORshiftLL` before slice G59 group U) empties it;
`stepLoc` runs `v29` to `.int .w64 0xC000005` in `R1`; it holds an arm64 op; its activation is
`0`. -/
def gFacts : Bool :=
  (checkG58 lc0 ps bs g).toOption == some (tab59, kt59) && ps.toList.all (·.id < 2 ^ 32) &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty && lc.ctx.f.blocks.toList.contains 4 &&
    (lc.ctx.f.block? 4).isSome && (lc.ctx.f.value? 29).isSome && blk.values[6]? == some 29 &&
    (val 29).op == .ARM64ORshiftLL && (kAt lc kt59 4 blk 6).get 1 == some 64 &&
    (kAt lc kt59 4 blk 6).get 2 == some 32 && (kAt lc kt59 4 blk 6).get 3 == some 64 &&
    uL35 lc (uIn35 lc 4) blk 6 == [(3, 8, false), (1, 32, false), (2, 32, false)] &&
    uL35 lc (uIn35 lc 4) blk 7 == [(3, 8, false), (2, 32, false)] &&
    uStep34 lc (uL35 lc (uIn35 lc 4) blk 6) (val 29) == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 29)) (fun s1 => isRes s1.regs[1]?) &&
    lc.ctx.f.lowered && lc.ctx.act == 0

theorem g59u_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    checkG58 lc0 ps bs g = .ok (tab59, kt59) ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      4 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 4 = some blk ∧
      lc.ctx.f.value? 29 = some (val 29) ∧ blk.values[6]? = some 29 ∧
      (val 29).op = .ARM64ORshiftLL ∧ (kAt lc kt59 4 blk 6).get 1 = some 64 ∧
      (kAt lc kt59 4 blk 6).get 2 = some 32 ∧ (kAt lc kt59 4 blk 6).get 3 = some 64 ∧
      uL35 lc (uIn35 lc 4) blk 6 = [(3, 8, false), (1, 32, false), (2, 32, false)] ∧
      uL35 lc (uIn35 lc 4) blk 7 = [(3, 8, false), (2, 32, false)] ∧
      uStep34 lc (uL35 lc (uIn35 lc 4) blk 6) (val 29) = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 29)) (fun s1 => isRes s1.regs[1]?) = true ∧
      lc.ctx.f.lowered = true ∧ lc.ctx.act = 0 := by
  have hf := g59u_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    List.all_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hres, hlt, hav, hsl, hm4, hbs, hvs, hi, hop, hk1, hk2, hk3, hu6, hu7, hold, hrun, hl,
    hact⟩ := hf
  refine ⟨?_, hlt, hav, hsl, hm4, ?_, ?_, hi, hop, hk1, hk2, hk3, hu6, hu7, hold, hrun, hl, hact⟩
  · revert hres; cases checkG58 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem env59 (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G49Env lc g L ps 0 tab59 E59 where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
            link := rfl
            pcOf := rfl
            retOut := fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := GenG48.addrAgree48
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

/-! ## `v29`: `ORR R3<<26, R1, R1` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 1 ∧ x = .int .w64 5) ∨ (r = 2 ∧ x = .int .w32 7) ∨ (r = 3 ∧ x = .int .w64 3) ∨
      x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    by_cases h1 : r = 1
    · subst h1; simp
    · by_cases h2 : r = 2
      · subst h2; simp
      · by_cases h3 : r = 3
        · subst h3; simp
        · simp [h1, h2, h3]
  · cases h

theorem locMatch59 : LocMatch E59 s0 4 6 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show m0.x _ = _ ∨ _; exact .inl (by simp only [m0]; decide)
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show (m0.x _).setWidth _ = _; simp only [m0]; decide
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show m0.x _ = _ ∨ _; exact .inl (by simp only [m0]; decide)
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E59]; decide,
    by simp only [MState.word, readMem, m0, E59]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

/-- `s0` under any class map with `R1`, `R3` at 64 and `R2` at 32 bits, in the mode `outSP`
(`SepFromW` of the empty memory). -/
theorem inv59 {K : KMap} (hk1 : K.get 1 = some 64) (hk2 : K.get 2 = some 32)
    (hk3 : K.get 3 = some 64) : G3Inv E59 lc K s0 E59.outSP where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, by simp [KeysNodup, GenG2.mem0],
      fun b al a h => by simp [GenG2.mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [hk1] at hc; cases hc; rfl
    · rw [hk2] at hc; cases hc; rfl
    · rw [hk3] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- `SPInv`: `outargs 0` at `SP`; the Go register `SP` holds `poison`. -/
theorem spInv59 (hact : lc.ctx.act = 0) : SPInv E59 s0 := by
  refine fun _ => ⟨?_, fun x hx => ?_⟩
  · show GenG48.ι48 (.outargs lc.ctx.act) = some GenG48.spO
    rw [hact]
    rfl
  · rcases s0_regs hx with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | rfl
    all_goals first | (simp [spReg] at h; done) | trivial

/-- An entry of a register below `R18` holds when its X register is so extended. -/
theorem uok_lt18 {m : MState} {r c : Nat} {sg : Bool} (hr : r < 18)
    (h : ExtOK (m.x (BitVec.ofNat 5 r)) c sg) : UOK m (some (r, c, sg)) := by
  intro k hk hobj
  simp only [objX?, hr, ↓reduceIte, Option.some.injEq] at hobj
  have hrk := ofNat5_inj (by omega) (by omega) hobj
  subst hrk
  exact h

/-- G35's table before `v29` holds of `m0`: `X3 = 3` a byte, `X1 = 5` and `X2 = 7` words. -/
theorem uokl0 : UOKL m0 [(3, 8, false), (1, 32, false), (2, 32, false)] := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact uok_lt18 (by decide) (by unfold ExtOK; simp only [m0]; decide)
  · exact uok_lt18 (by decide) (by unfold ExtOK; simp only [m0]; decide)
  · exact uok_lt18 (by decide) (by unfold ExtOK; simp only [m0]; decide)

/-- None of G54's premises applies to `ORshiftLL`. -/
theorem pre29 {s : LocState} (hop : (val 29).op = .ARM64ORshiftLL) : G54Pre lc s (val 29) := by
  have hne : ∀ o : Op, o ≠ .ARM64ORshiftLL → (val 29).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩,
    ?_, ?_⟩, ?_⟩, ?_, ?_⟩
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
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))

/-- **G59, group U, on `runtime.(*scavChunkData).pack`** (`func (sc *scavChunkData) pack()
uint64`, on arm64 `LDPW (R0), (R1, R2)`, `MOVBU 8(R0), R3`, `ORR R3<<26, R1, R1`,
`ORR R2<<32, R1, R0`): `checkG58` accepts the function; G34's step across `v29 = ORshiftLL`, G35's
before slice G59 group U, empties the upper-bit table, which now keeps `R3`'s and `R2`'s entries
for `v31 = MOVDnop v5`. In an activation whose `outargs` block sits at `SP` (`outSP`, `SPInv`), from
`s0`, with `R1 = 5`, `R2 = 7`, `R3 = 3`, `stepLoc` runs `v29` to `0xC000005` in `R1`, and
`g58_value` relates it to a machine run of its `ORR` (Prog 10) to a state whose `X1` holds
`0xC000005` (`ValRel`) and whose `X2` is still the zero extension of its low 32 bits (the table's
`R2` entry), under an activation extending `E59` that is again a `G49Env`. -/
theorem genG59u_witness :
    checkG58 lc0 ps bs g = .ok (tab59, kt59) ∧
      uStep34 lc (uL35 lc (uIn35 lc 4) blk 6) (val 29) = [] ∧
      uL35 lc (uIn35 lc 4) blk 7 = [(3, 8, false), (2, 32, false)] ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 29) = .ok s1 ∧
        s1.regs[1]? = some (.int .w64 0xC000005) ∧
        E59.Extends E1 ∧ G49Env lc g L ps 0 tab59 E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 4 7 m1 ∧ ValRel E1.ι (.int .w64 0xC000005) (m1.x 1) ∧
        ExtOK (m1.x 2) 32 false := by
  obtain ⟨hc, hlt, hav, hsl, hm4, hb, hv, hi, hop, hk1, hk2, hk3, hu6, hu7, hold, hrun, hl,
    hact⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr1 := isRes_spec hr
  have hE := env59 hlt hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64ORshiftLL → (val 29).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g58_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 4 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm4
  have hb0 : lc0.ctx.f.block? 4 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 29 = some (val 29) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, -, -, hu1⟩ := g58_value (H := GenG2.H0)
    (env := GenG2.env) hc hE hl0 hm0 hb0 hi hv0 (by rw [hop]; rfl) locMatch59 (inv59 hk1 hk2 hk3)
    (fun _ => spInv59 hact) (fun _ => rfl) (fun _ => rfl)
    (by
      change UOKL m0 (uL35 lc (uIn35 lc 4) blk 6)
      rw [hu6]
      exact uokl0)
    (pre29 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun _ h => absurd h (hne _ (by decide))) hs1
  have hu1' : UOKL m1 [(3, 8, false), (2, 32, false)] := by
    change UOKL m1 (uL35 lc (uIn35 lc 4) blk 7) at hu1
    rwa [hu7] at hu1
  refine ⟨hc, hold, hu7, s1, E1, m1, hs1, hr1, hx1, hE1, hp1, hm1,
    (hm1.regs 1 _ hr1).1 1 (by simp [objX?]), ?_⟩
  exact hu1' (2, 32, false) (by simp) 2 (by decide) (by simp [objX?])

end GoFV.Proof.Witness.GenG59u
