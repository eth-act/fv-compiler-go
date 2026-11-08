import GoFV.Proof.Gen.G21
import GoFV.Proof.Witness.GenG20

/-!
# Non-vacuity witness: slice G21 of the genssa validator on `(*queueOnePass).next` (std/regexp)

`std/std/regexp/%28%2AqueueOnePass%29.next,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`):
`(*queueOnePass).next` (`regexp/onepass.go`), `n = q.dense[q.nextIndex]; q.nextIndex++`.

`checkG20` rejects it (`v15 = MOVDreg`); `checkG21` accepts it with the PC table `tab` and the
class table `kt`. Block `b1`: `v13 = MOVWUload [52] v6 v1` (`MOVWU 52(R0), R3`, the zero extension
of `q.nextIndex`) and `v15 = MOVDreg v13` (`MOVD R3, R4`), whose upper-bit table entry
`uAt lc blk1 6 = (R3, 32, unsigned)` comes from `v13`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g21_facts`),
`stepLoc` runs `v13` and `v15` from a state with `q` the start of `heap 1` in `R0` and
`q.nextIndex = 0xffff_fffe` (`memH`): `R3` then holds the 32-bit and `R4` the 64-bit integer
`0xffff_fffe`, the zero extension that `signOf v13` names. On a framed activation with `G10Env`
(as `GenG14`'s, `heap 1` at `2^41`) and the machine memory holding those bytes there (`MH`),
`g21_value` runs the load, whose upper-bit invariant `UOK` makes the machine's `X3` the zero
extension, and then the `MOVD`: the machine's `X4` is `0x0000_0000_ffff_fffe`
(`genG21_value_witness`), which a sign extension (`0xffff_ffff_ffff_fffe`) would not be.
-/

namespace GoFV.Proof.Witness.GenG21

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/regexp/%28%2AqueueOnePass%29.next,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "regexp"
func "(*queueOnePass).next" 1 0 0
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
config localpkg "regexp"
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
type t5 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t4 SLICE 24 8 8 hasptr "[]uint32" "[]uint32" t5
type t3 STRUCT 56 8 32 hasptr,named "queueOnePass" "regexp.queueOnePass" 4
field 0 "sparse" t4 0 0
field 1 "dense" t4 24 0
field 2 "size" t5 48 0
field 3 "nextIndex" t5 52 0
type t2 PTR 8 8 8 hasptr,direct,comparable "*queueOnePass" "*regexp.queueOnePass" t3
type t1 FUNC 8 8 8 hasptr,direct "method(*queueOnePass) func() uint32" "method(*regexp.queueOnePass) func() uint32" 1 0 1
field 0 "q" t2 ? 0
field 1 "n" t5 ? 0
aux a2 sym "regexp.(*queueOnePass).next" "regexp.(*queueOnePass).next" 1 - 0 - - - - 0
posbase p2 "regexp/onepass.go" 1 1 -1
aux a3 name "q" "q" PPARAM t2 0 1 used p2:106:7:0:0
aux a4 name "n" "n" PPARAMOUT t5 0 1 used p2:106:32:0:0
aux a1 call "AuxCall{regexp.(*queueOnePass).next}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t5 a4 0 -1
type t6 BOOL 1 1 0 comparable,named "bool" "bool"
type t7 INT8 1 1 0 comparable,named "int8" "int8"
type t8 INT16 2 2 0 comparable,named "int16" "int16"
type t9 INT32 4 4 0 comparable,named "int32" "int32"
type t10 INT64 8 8 0 comparable,named "int64" "int64"
type t11 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t12 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t13 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t14 INT 8 8 0 comparable,named "int" "int"
type t15 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t16 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t17 UINT 8 8 0 comparable,named "uint" "uint"
type t18 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t19 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t11
type t21 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t9
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
type t36 PTR 8 8 8 hasptr,direct,comparable "**queueOnePass" "**regexp.queueOnePass" t2
type t37 PTR 8 8 8 hasptr,direct,comparable "*[]uint32" "*[]uint32" t4
aux a5 type "uint32" t5
type t38 RESULTS ? ? ? - "uint32,mem" "" 2 t5,t31
slot s1 a3 t2 0 - 0
f b1 t1 a1 32 3
typs Bool=t6,Int8=t7,Int16=t8,Int32=t9,Int64=t10,UInt8=t11,UInt16=t12,UInt32=t5,UInt64=t13,Int=t14,Float32=t15,Float64=t16,UInt=t17,Uintptr=t18,String=t19,BytePtr=t20,Int32Ptr=t21,UInt32Ptr=t22,IntPtr=t23,UintptrPtr=t24,Float32Ptr=t25,Float64Ptr=t26,BytePtrPtr=t27,Complex64=t28,Complex128=t29,UnsafePtr=t30,Mem=t31,Flags=t32,Void=t33,Int128=t34,ResultMem=t35
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t22 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:106:6:2:0 3 -
v v7 Const32 t5 0 - p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p2:107:7:0:0 1 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 1 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 1 v11
v v13 Load t5 0 - p2:107:15:0:0 1 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 PtrIndex t22 0 - p2:107:13:0:0 1 v19,v15
v v21 Copy t31 0 - p2:107:13:2:0 5 v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v21
v v23 Copy t2 0 - p2:108:3:2:0 2 v6
v v24 NilCheck t2 0 - p2:108:3:0:0 1 v23,v21
v v25 OffPtr t22 52 - p2:108:3:0:0 1 v24
v v26 Load t5 0 - p2:108:3:0:0 1 v25,v21
v v28 Add32 t5 0 - p2:108:13:0:0 1 v26,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 1 v23,v21
v v30 OffPtr t22 52 - p2:108:3:0:0 1 v29
v v31 Store t31 0 a5 p2:108:13:0:0 1 v30,v28,v21
v v32 MakeResult t38 0 - p2:109:2:0:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v17 Copy t31 0 - p2:107:13:2:0 1 v1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v17
names s1
named s1 v6,v23
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,1=v27
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t22 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:106:6:2:0 3 -
v v7 Const32 t5 0 - p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p2:107:7:1:0 1 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 1 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 1 v11
v v13 Load t5 0 - p2:107:15:0:0 1 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 PtrIndex t22 0 - p2:107:13:0:0 1 v19,v15
v v21 Copy t31 0 - p2:107:13:2:0 5 v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v21
v v23 Copy t2 0 - p2:108:3:2:0 2 v6
v v24 NilCheck t2 0 - p2:108:3:1:0 1 v23,v21
v v25 OffPtr t22 52 - p2:108:3:0:0 1 v24
v v26 Load t5 0 - p2:108:3:0:0 1 v25,v21
v v28 Add32 t5 0 - p2:108:13:0:0 1 v26,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 1 v23,v21
v v30 OffPtr t22 52 - p2:108:3:0:0 1 v29
v v31 Store t31 0 a5 p2:108:13:0:0 1 v30,v28,v21
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v17 Copy t31 0 - p2:107:13:2:0 1 v1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v17
names s1
named s1 v6,v23
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,1=v27
freev -
freeb -
cache postorder b2,b3,b1
cache linestarts 2:107:109
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 14 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t22 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:106:6:2:0 5 -
v v7 Const32 t5 0 - p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p2:107:7:1:0 1 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 1 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 1 v11
v v13 Load t5 0 - p2:107:15:0:0 1 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 PtrIndex t22 0 - p2:107:13:0:0 1 v19,v15
v v21 Copy t31 0 - p2:107:13:2:0 0 v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v23 Copy t2 0 - p2:108:3:2:0 0 v6
v v24 NilCheck t2 0 - p2:108:3:1:0 1 v6,v1
v v25 OffPtr t22 52 - p2:108:3:0:0 1 v24
v v26 Load t5 0 - p2:108:3:0:0 1 v25,v1
v v28 Add32 t5 0 - p2:108:13:0:0 1 v26,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 1 v6,v1
v v30 OffPtr t22 52 - p2:108:3:0:0 1 v29
v v31 Store t31 0 a5 p2:108:13:0:0 1 v30,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v17 Copy t31 0 - p2:107:13:2:0 0 v1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6,v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,1=v27
freev -
freeb -
cache postorder b2,b3,b1
cache linestarts 2:107:109
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 10 -
v v6 Arg t2 0 a3 p2:106:6:2:0 4 -
v v8 NilCheck t2 0 - p2:107:7:1:0 1 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 1 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 1 v11
v v13 Load t5 0 - p2:107:15:0:0 1 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 PtrIndex t22 0 - p2:107:13:0:0 1 v19,v15
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v24 NilCheck t2 0 - p2:108:3:1:0 1 v6,v1
v v25 OffPtr t22 52 - p2:108:3:0:0 1 v24
v v26 Load t5 0 - p2:108:3:0:0 1 v25,v1
v v28 Add32 t5 0 - p2:108:13:0:0 1 v26,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 1 v6,v1
v v30 OffPtr t22 52 - p2:108:3:0:0 1 v29
v v31 Store t31 0 a5 p2:108:13:0:0 1 v30,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v17,v23,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:107:109
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 10 -
v v6 Arg t2 0 a3 p2:106:6:2:0 4 -
v v8 NilCheck t2 0 - p2:107:7:1:0 1 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 1 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 1 v11
v v13 Load t5 0 - p2:107:15:0:0 1 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 PtrIndex t22 0 - p2:107:13:0:0 1 v19,v15
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v24 NilCheck t2 0 - p2:108:3:1:0 1 v6,v1
v v25 OffPtr t22 52 - p2:108:3:0:0 1 v24
v v26 Load t5 0 - p2:108:3:0:0 1 v25,v1
v v28 Add32 t5 0 - p2:108:13:0:0 1 v26,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 1 v6,v1
v v30 OffPtr t22 52 - p2:108:3:0:0 1 v29
v v31 Store t31 0 a5 p2:108:13:0:0 1 v30,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v17,v23,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:107:109
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 10 -
v v6 Arg t2 0 a3 p2:106:6:2:0 4 -
v v8 NilCheck t2 0 - p2:107:7:1:0 1 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 1 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 1 v11
v v13 Load t5 0 - p2:107:15:0:0 1 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 PtrIndex t22 0 - p2:107:13:0:0 1 v19,v15
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v24 NilCheck t2 0 - p2:108:3:1:0 1 v6,v1
v v25 OffPtr t22 52 - p2:108:3:0:0 1 v24
v v26 Load t5 0 - p2:108:3:0:0 1 v25,v1
v v28 Add32 t5 0 - p2:108:13:0:0 1 v26,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 1 v6,v1
v v30 OffPtr t22 52 - p2:108:3:0:0 1 v29
v v31 Store t31 0 a5 p2:108:13:0:0 1 v30,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v17,v23,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:107:109
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 10 -
v v6 Arg t2 0 a3 p2:106:6:2:0 4 -
v v8 NilCheck t2 0 - p2:107:7:1:0 1 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 1 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 1 v11
v v13 Load t5 0 - p2:107:15:0:0 1 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 PtrIndex t22 0 - p2:107:13:0:0 1 v19,v15
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v24 NilCheck t2 0 - p2:108:3:1:0 1 v6,v1
v v25 OffPtr t22 52 - p2:108:3:0:0 1 v24
v v26 Load t5 0 - p2:108:3:0:0 1 v25,v1
v v28 Add32 t5 0 - p2:108:13:0:0 1 v26,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 1 v6,v1
v v30 OffPtr t22 52 - p2:108:3:0:0 1 v29
v v31 Store t31 0 a5 p2:108:13:0:0 1 v30,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v17,v23,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:107:109
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 10 -
v v6 Arg t2 0 a3 p2:106:6:2:0 4 -
v v8 NilCheck t2 0 - p2:107:7:1:0 1 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 1 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 1 v11
v v13 Load t5 0 - p2:107:15:0:0 1 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v24 NilCheck t2 0 - p2:108:3:1:0 1 v6,v1
v v25 OffPtr t22 52 - p2:108:3:0:0 1 v24
v v26 Load t5 0 - p2:108:3:0:0 1 v25,v1
v v28 Add32 t5 0 - p2:108:13:0:0 1 v26,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 1 v6,v1
v v30 OffPtr t22 52 - p2:108:3:0:0 1 v29
v v31 Store t31 0 a5 p2:108:13:0:0 1 v30,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v17 Mul64 t14 0 - p2:107:13:0:0 1 v15,v23
v v23 Const64 t14 4 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:107:109
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 10 -
v v6 Arg t2 0 a3 p2:106:6:2:0 4 -
v v8 NilCheck t2 0 - p2:107:7:1:0 1 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 1 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 1 v11
v v13 Load t5 0 - p2:107:15:0:0 1 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v23 Const64 t14 4 - p2:107:13:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v24 NilCheck t2 0 - p2:108:3:1:0 1 v6,v1
v v25 OffPtr t22 52 - p2:108:3:0:0 1 v24
v v26 Load t5 0 - p2:108:3:0:0 1 v25,v1
v v28 Add32 t5 0 - p2:108:13:0:0 1 v26,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 1 v6,v1
v v30 OffPtr t22 52 - p2:108:3:0:0 1 v29
v v31 Store t31 0 a5 p2:108:13:0:0 1 v30,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v17 Mul64 t14 0 - p2:107:13:0:0 1 v15,v23
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:107:109
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 10 -
v v6 Arg t2 0 a3 p2:106:6:2:0 4 -
v v8 NilCheck t2 0 - p2:107:7:1:0 1 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 1 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 1 v11
v v13 Load t5 0 - p2:107:15:0:0 1 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v23 Const64 t14 4 - p2:107:13:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v24 NilCheck t2 0 - p2:108:3:1:0 1 v6,v1
v v25 OffPtr t22 52 - p2:108:3:0:0 1 v24
v v26 Load t5 0 - p2:108:3:0:0 1 v25,v1
v v28 Add32 t5 0 - p2:108:13:0:0 1 v26,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 1 v6,v1
v v30 OffPtr t22 52 - p2:108:3:0:0 1 v29
v v31 Store t31 0 a5 p2:108:13:0:0 1 v30,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v17 Mul64 t14 0 - p2:107:13:0:0 1 v15,v23
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:107:109
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 10 -
v v6 Arg t2 0 a3 p2:106:6:2:0 4 -
v v8 NilCheck t2 0 - p2:107:7:1:0 4 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 0 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 3 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v23 Const64 t14 4 - p2:107:13:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v24 NilCheck t2 0 - p2:108:3:1:0 0 v6,v1
v v25 OffPtr t22 52 - p2:108:3:0:0 0 v8
v v26 Load t5 0 - p2:108:3:0:0 0 v12,v1
v v28 Add32 t5 0 - p2:108:13:0:0 1 v13,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 0 v6,v1
v v30 OffPtr t22 52 - p2:108:3:0:0 0 v8
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v17 Mul64 t14 0 - p2:107:13:0:0 1 v15,v23
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 10 -
v v6 Arg t2 0 a3 p2:106:6:2:0 4 -
v v8 NilCheck t2 0 - p2:107:7:1:0 4 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 0 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 3 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v23 Const64 t14 4 - p2:107:13:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v24 NilCheck t2 0 - p2:108:3:1:0 0 v6,v1
v v25 OffPtr t22 52 - p2:108:3:0:0 0 v8
v v26 Load t5 0 - p2:108:3:0:0 0 v12,v1
v v28 Add32 t5 0 - p2:108:13:0:0 1 v13,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 0 v6,v1
v v30 OffPtr t22 52 - p2:108:3:0:0 0 v8
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v17 Mul64 t14 0 - p2:107:13:0:0 1 v15,v23
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 9 -
v v6 Arg t2 0 a3 p2:106:6:2:0 4 -
v v8 NilCheck t2 0 - p2:107:7:1:0 2 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v11 NilCheck t2 0 - p2:107:15:0:0 0 v6,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v23 Const64 t14 4 - p2:107:13:0:0 1 -
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v24 NilCheck t2 0 - p2:108:3:1:0 0 v6,v1
v v28 Add32 t5 0 - p2:108:13:0:0 1 v13,v27
v v29 NilCheck t2 0 - p2:108:3:0:0 0 v6,v1
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v17 Mul64 t14 0 - p2:107:13:0:0 1 v15,v23
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v30,v26,v25,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v6 Arg t2 0 a3 p2:106:6:2:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v23 Const64 t14 4 - p2:107:13:0:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v8 NilCheck t2 0 - p2:107:7:1:0 5 v6,v1
v v11 Copy t2 0 - p2:107:15:0:0 0 v8
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v29 Copy t2 0 - p2:108:3:0:0 0 v8
v v24 Copy t2 0 - p2:108:3:1:0 0 v8
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v17 Mul64 t14 0 - p2:107:13:0:0 1 v15,v23
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v30,v26,v25,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p2:106:6:2:0 1 -
v v23 Const64 t14 4 - p2:107:13:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 5 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v11 Copy t2 0 - p2:107:15:0:0 0 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Mul64 t14 0 - p2:107:13:0:0 1 v15,v23
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v24 Copy t2 0 - p2:108:3:1:0 0 v8
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v29 Copy t2 0 - p2:108:3:0:0 0 v8
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v30,v26,v25,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p2:106:6:2:0 1 -
v v23 Const64 t14 4 - p2:107:13:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 2 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Mul64 t14 0 - p2:107:13:0:0 1 v15,v23
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v29,v24,v11,v30,v26,v25,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p2:106:6:2:0 1 -
v v23 Const64 t14 4 - p2:107:13:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 2 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Mul64 t14 0 - p2:107:13:0:0 1 v15,v23
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v29,v24,v11,v30,v26,v25,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p2:106:6:2:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 2 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v23,v24,v11,v30,v26,v25,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p2:106:6:2:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 2 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v23,v24,v11,v30,v26,v25,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p2:106:6:2:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 2 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v23,v24,v11,v30,v26,v25,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 20 "expand calls"
aux a6 nameoff "q+0" a3 0
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 2 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v10 Load t4 0 - p2:107:7:0:0 2 v9,v1
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v14 SliceLen t14 0 - p2:107:13:0:0 2 v10
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v14
v v23 SB t18 0 - p0:0:0:0:0 0 -
v v24 SP t18 0 - p0:0:0:0:0 2 -
v v11 OffPtr t36 0 - p0:0:0:0:0 0 v24
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v19 SlicePtr t22 0 - p2:107:13:0:0 1 v10
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v19,v17
v v31 Store t31 0 a5 p2:108:13:0:0 2 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
v v30 LocalAddr t22 0 a4 p2:109:2:1:0 0 v24,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v11,1=v27
freev v26,v25,v21,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 2 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 3 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v10 SliceMake t4 0 - p2:107:7:0:0 0 v26,v25,v7
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v25
v v23 SB t18 0 - p0:0:0:0:0 0 -
v v24 SP t18 0 - p0:0:0:0:0 2 -
v v11 OffPtr t36 0 - p0:0:0:0:0 0 v24
v v26 Load t22 0 - p2:107:7:0:0 2 v9,v1
v v25 Load t14 0 - p2:107:7:0:0 3 v21,v1
v v21 OffPtr t23 8 - p2:107:7:0:0 1 v9
v v7 Load t14 0 - p2:107:7:0:0 1 v5,v1
v v5 OffPtr t23 16 - p2:107:7:0:0 1 v9
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v26,v17
v v31 Store t31 0 a5 p2:108:13:0:0 2 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
v v30 LocalAddr t22 0 a4 p2:109:2:1:0 0 v24,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v11,1=v27
freev v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 2 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 3 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v10 SliceMake t4 0 - p2:107:7:0:0 0 v26,v25,v7
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v25
v v23 SB t18 0 - p0:0:0:0:0 0 -
v v24 SP t18 0 - p0:0:0:0:0 2 -
v v11 OffPtr t36 0 - p0:0:0:0:0 0 v24
v v26 Load t22 0 - p2:107:7:0:0 2 v9,v1
v v25 Load t14 0 - p2:107:7:0:0 3 v21,v1
v v21 OffPtr t23 8 - p2:107:7:0:0 1 v9
v v7 Load t14 0 - p2:107:7:0:0 1 v5,v1
v v5 OffPtr t23 16 - p2:107:7:0:0 1 v9
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v26,v17
v v31 Store t31 0 a5 p2:108:13:0:0 2 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
v v30 LocalAddr t22 0 a4 p2:109:2:1:0 0 v24,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v11,1=v27
freev v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 8 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 2 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 3 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v10 SliceMake t4 0 - p2:107:7:0:0 0 v26,v25,v7
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v25
v v23 SB t18 0 - p0:0:0:0:0 0 -
v v24 SP t18 0 - p0:0:0:0:0 2 -
v v11 OffPtr t36 0 - p0:0:0:0:0 0 v24
v v26 Load t22 0 - p2:107:7:0:0 2 v9,v1
v v25 Load t14 0 - p2:107:7:0:0 3 v21,v1
v v21 OffPtr t23 8 - p2:107:7:0:0 1 v9
v v7 Load t14 0 - p2:107:7:0:0 1 v5,v1
v v5 OffPtr t23 16 - p2:107:7:0:0 1 v9
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v26,v17
v v31 Store t31 0 a5 p2:108:13:0:0 2 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
v v30 LocalAddr t22 0 a4 p2:109:2:1:0 0 v24,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v11,1=v27
freev v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v25
v v26 Load t22 0 - p2:107:7:0:0 1 v9,v1
v v25 Load t14 0 - p2:107:7:0:0 2 v21,v1
v v21 OffPtr t23 32 - p2:107:7:0:0 1 v8
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v26,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v30,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v25
v v26 Load t22 0 - p2:107:7:0:0 1 v9,v1
v v25 Load t14 0 - p2:107:7:0:0 2 v21,v1
v v21 OffPtr t23 32 - p2:107:7:0:0 1 v8
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v26,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v30,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v25
v v26 Load t22 0 - p2:107:7:0:0 1 v9,v1
v v25 Load t14 0 - p2:107:7:0:0 2 v21,v1
v v21 OffPtr t23 32 - p2:107:7:0:0 1 v8
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v26,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v30,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v25
v v26 Load t22 0 - p2:107:7:0:0 1 v9,v1
v v25 Load t14 0 - p2:107:7:0:0 2 v21,v1
v v21 OffPtr t23 32 - p2:107:7:0:0 1 v8
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v26,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v30,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v25
v v26 Load t22 0 - p2:107:7:0:0 1 v9,v1
v v25 Load t14 0 - p2:107:7:0:0 2 v21,v1
v v21 OffPtr t23 32 - p2:107:7:0:0 1 v8
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v26,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v30,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v25
v v26 Load t22 0 - p2:107:7:0:0 1 v9,v1
v v25 Load t14 0 - p2:107:7:0:0 2 v21,v1
v v21 OffPtr t23 32 - p2:107:7:0:0 1 v8
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v26,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v30,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v25
v v26 Load t22 0 - p2:107:7:0:0 1 v9,v1
v v25 Load t14 0 - p2:107:7:0:0 2 v21,v1
v v21 OffPtr t23 32 - p2:107:7:0:0 1 v8
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v26,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v30,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v25
v v26 Load t22 0 - p2:107:7:0:0 1 v9,v1
v v25 Load t14 0 - p2:107:7:0:0 2 v21,v1
v v21 OffPtr t23 32 - p2:107:7:0:0 1 v8
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v26,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v30,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 32 3
b b1 If p2:107:15:0:0 1 0 - v16 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v27 Const32 t5 1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v9 OffPtr t37 24 - p2:107:7:0:0 1 v8
v v12 OffPtr t22 52 - p2:107:15:0:0 2 v8
v v13 Load t5 0 - p2:107:15:0:0 2 v12,v1
v v15 ZeroExt32to64 t14 0 - p2:107:13:0:0 3 v13
v v16 IsInBounds t6 0 - p2:107:13:0:0 1 v15,v25
v v26 Load t22 0 - p2:107:7:0:0 1 v9,v1
v v25 Load t14 0 - p2:107:7:0:0 2 v21,v1
v v21 OffPtr t23 32 - p2:107:7:0:0 1 v8
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v17 Lsh64x64 t14 1 - p2:107:13:0:0 1 v15,v29
v v28 Add32 t5 0 - p2:108:13:1:0 1 v13,v27
v v20 AddPtr t22 0 - p2:107:13:0:0 1 v26,v17
v v31 Store t31 0 a5 p2:108:13:0:0 1 v12,v28,v1
v v22 Load t5 0 - p2:107:13:0:0 1 v20,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
v v29 Const64 t13 2 - p2:107:13:0:0 1 -
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 PanicBounds t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 1=v27
freev v30,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 4 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVWUreg t14 0 - p2:107:13:0:0 3 v13
v v26 ARM64MOVDload t22 24 - p2:107:7:0:0 1 v8,v1
v v25 ARM64MOVDload t14 32 - p2:107:7:0:0 2 v8,v1
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v29,v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 4 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVWUreg t14 0 - p2:107:13:0:0 3 v13
v v26 ARM64MOVDload t22 24 - p2:107:7:0:0 1 v8,v1
v v25 ARM64MOVDload t14 32 - p2:107:7:0:0 2 v8,v1
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v29,v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 4 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 ARM64MOVDload t22 24 - p2:107:7:0:0 1 v8,v1
v v25 ARM64MOVDload t14 32 - p2:107:7:0:0 2 v8,v1
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v29,v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 36 "pair"
type t39 TUPLE ? ? ? - "*uint32,int" "" t22 t14
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2
cache linestarts 2:107:109
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:107:7:1:0 3 v6,v1
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v8,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v8,v1
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v8,v28,v1
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 4 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v8 ARM64LoweredNilCheck t33 0 - p2:107:7:1:0 0 v6,v1
v v29 ARM64LDP t39 24 - p2:107:7:0:0 2 v6,v1
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v6,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v6,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v29 ARM64LDP t39 24 - p2:107:7:1:0 2 v6,v1
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v6,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v6,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v29 ARM64LDP t39 24 - p2:107:7:1:0 2 v6,v1
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v6,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v6,v28,v1
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v22,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v20,v17,v21,v16,v12,v9,v27,v5,v7,v11,v24,v23,v10,v19,v14,v4,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{regexp.(*queueOnePass).next}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t5 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v29 ARM64LDP t39 24 - p2:107:7:1:0 2 v6,v1
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v6,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v6,v28,v1
v v20 Copy t5 0 - p2:109:2:2:0 1 v22
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v20,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v9,v10,v11,v12,v14,v16,v17,v19,v21,v23,v24,v27
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
fstate scheduled,laidout
regalloc 33 v6:R0,v13:R3,v15:R4,v20:R0,v22:R1,v25:R2,v26:R1,v28:R2,v29:(R1;R2),v32:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v29 ARM64LDP t39 24 - p2:107:7:1:0 2 v6,v1
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v6,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v6,v28,v1
v v20 Copy t5 0 - p2:109:2:2:0 1 v22
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v20,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v9,v10,v11,v12,v14,v16,v17,v19,v21,v23,v24,v27
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
fstate scheduled,laidout
regalloc 33 v6:R0,v13:R3,v15:R4,v20:R0,v22:R1,v25:R2,v26:R1,v28:R2,v29:(R1;R2),v32:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 32 3
b b1 ARM64ULT p2:107:15:0:0 1 0 - v30 b2:0,b3:0 -
v v6 ArgIntReg t2 0 a6 p2:107:15:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v29 ARM64LDP t39 24 - p2:107:7:1:0 2 v6,v1
v v25 Select1 t14 0 - p2:107:7:0:0 2 v29
v v26 Select0 t22 0 - p2:107:7:0:0 1 v29
v v13 ARM64MOVWUload t5 52 - p2:107:15:0:0 2 v6,v1
v v15 ARM64MOVDreg t14 0 - p2:107:13:0:0 3 v13
v v30 ARM64CMP t32 0 - p2:107:13:0:0 1 v15,v25
b b2 Ret p2:109:2:1:0 0 0 - v32 - b1:0
v v22 ARM64MOVWUloadidx4 t5 0 - p2:107:13:0:0 1 v26,v15,v1
v v28 ARM64ADDconst t5 1 - p2:108:13:1:0 1 v13
v v31 ARM64MOVWstore t31 52 - p2:108:13:0:0 1 v6,v28,v1
v v20 Copy t5 0 - p2:109:2:2:0 1 v22
v v32 MakeResult t38 0 - p2:109:2:1:0 1 v20,v31
b b3 Exit p2:107:15:0:0 0 0 - v18 - b1:1
v v18 ARM64LoweredPanicBoundsRR t31 0 - p2:107:13:0:0 1 v15,v25,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v9,v10,v11,v12,v14,v16,v17,v19,v21,v23,v24,v27
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:107:109
fstate scheduled,laidout
regalloc 33 v6:R0,v13:R3,v15:R4,v20:R0,v22:R1,v25:R2,v26:R1,v28:R2,v29:(R1;R2),v32:[]
dcllen 2
end
frontend
end
ptrcache t3,t5,t8,t9,t10,t11,t13,t14,t15,t16,t18,t19,t20,t24,t27,t30
typelink t31=t35
typeorder t7,t11,t8,t12,t9,t5,t10,t13,t14,t17,t18,t28,t29,t15,t16,t6,t20,t21,t22,t23,t24,t25,t26,t27,t36,t37,t2,t1,t4,t3,t19,t30,t31,t33,t32,t34,t39,t35,t38
eof
"#

/-- `std/std/regexp/%28%2AqueueOnePass%29.next,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "regexp"
func "(*queueOnePass).next" 1
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
type t1 8 8 8 1 01 "*queueOnePass"
name n1 "q" PPARAM t1 1 "regexp.q" 0 a3
type t2 4 4 0 0 - "uint32"
name n2 "n" PPARAMOUT t2 1 "regexp.n" 0 a4
in n1 0 used
in n2 0 used,outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p2 "regexp/onepass.go" 1 1 -1 1 "regexp/onepass.go" "regexp/onepass.go" 1 1
sym y1 "regexp.(*queueOnePass).next" 1
curfn p2:106:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 106 201080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "regexp.(*queueOnePass).next.arginfo1" 0
sym y5 "regexp.(*queueOnePass).next.argliveinfo" 0
sym y6 "runtime.panicBounds" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:106:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:106:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:106:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:106:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:106:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:106:6:2:0
p 6 6 0 0 0 - LDP 0 MEM/8192/0/0/NONE/0/24/-/- 0 - REGREG/8193/0/0/NONE/0/8194/-/- 0 0 p2:107:7:1:0
p 7 7 0 0 0 - MOVWU 0 MEM/8192/0/0/NONE/0/52/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p2:107:15:2:0
p 8 8 0 0 0 - MOVD 0 REG/8195/0/0/NONE/0/0/-/- 0 - REG/8196/0/0/NONE/0/0/-/- 0 0 p2:107:13:2:0
p 9 9 0 0 0 - CMP 0 REG/8194/0/0/NONE/0/0/-/- 8196 - _ 0 0 p2:107:13:2:0
p 10 10 0 0 0 - BHS 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@16 0 0 p2:107:15:2:0
p 11 11 0 0 0 - MOVWU 0 MEM/8193/8772/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:107:13:2:0
p 12 12 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/1/-/- 8195 - REG/8194/0/0/NONE/0/0/-/- 0 0 p2:108:13:1:0
p 13 13 0 0 0 - MOVW 0 REG/8194/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/52/-/- 0 0 p2:108:13:2:0
p 14 14 0 0 0 - MOVD 0 REG/8193/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:109:2:1:0
p 15 15 0 0 0 - RET 0 _ 0 - _ 0 0 p2:109:2:2:0
p 16 16 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:107:13:2:0
p 17 17 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/4/-/- 0 - CONST/0/0/0/NONE/0/2655/-/- 0 0 p2:107:13:2:0
p 18 18 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p2:107:13:2:0
p 19 19 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p2:107:15:0:0
p 20 20 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 106 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:2:20:50
dbgregout n2
dbgpc 2:20:15
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
sym y16 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p2:106:6:0:0
p 21 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:106:6:0:0
p 22 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:106:6:0:0
p 23 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:106:6:0:0
p 24 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@33 0 0 p2:106:6:0:0
p 25 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:106:6:0:0
p 26 12 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p2:106:6:0:1
p 27 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:106:6:0:0
p 28 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:106:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:106:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:106:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:106:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p2:106:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:106:6:2:0
p 6 24 0 0 245 - LDP 0 MEM/8192/0/0/NONE/87/24/-/- 0 - REGREG/8193/0/0/NONE/7/8194/-/- 0 0 p2:107:7:1:0
p 7 28 0 0 392 - MOVWU 0 MEM/8192/0/0/NONE/88/52/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:107:15:2:0
p 8 32 0 0 301 - MOVD 0 REG/8195/0/0/NONE/2/0/-/- 0 - REG/8196/0/0/NONE/2/0/-/- 0 0 p2:107:13:2:0
p 9 36 0 0 92 - CMP 0 REG/8194/0/0/NONE/2/0/-/- 8196 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:107:13:2:0
p 10 40 0 0 80 - BHS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/16/-/@16 0 0 p2:107:15:2:0
p 11 44 0 0 398 - MOVWU 0 MEM/8193/8772/0/NONE/114/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:107:13:2:0
p 12 48 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/1/-/- 8195 - REG/8194/0/0/NONE/2/0/-/- 0 0 p2:108:13:1:0
p 13 52 0 0 375 - MOVW 0 REG/8194/0/0/NONE/2/0/-/- 0 - MEM/8192/0/0/NONE/88/52/-/- 0 0 p2:108:13:2:0
p 14 56 0 0 301 - MOVD 0 REG/8193/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:109:2:1:0
p 15 60 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:109:2:2:0
p 29 64 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:109:2:2:0
p 30 68 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:109:2:2:0
p 16 72 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:107:13:2:0
p 17 72 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/4/-/- 0 - CONST/0/0/0/NONE/18/2655/-/- 0 0 p2:107:13:2:0
p 18 72 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y6/- 0 0 p2:107:13:2:0
p 19 76 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:107:15:0:0
p 31 80 -16 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:107:15:0:0
p 32 80 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:106:6:0:0
p 33 80 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:106:6:0:0
p 34 80 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p2:106:6:0:0
p 35 84 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:106:6:0:0
p 36 88 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y7/- 0 0 p2:106:6:0:0
p 37 92 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:106:6:0:0
p 38 92 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:106:6:0:0
p 39 96 16 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@21 0 0 p2:106:6:0:0
fn y1 8 8 0 0 106 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 112 0 900b40f9ff6330eb49020054fe0f1ff8fd831ff8fd2300d1018841a9033440b9e40303aa9f0002eb02010054217864b862040091023400b9e00301aafd835ff8fe0741f8c0035fd6000000941f2003d5e00700f9e3031eaa00000094e00740f9e8ffff17000000000000000000000000 2
reloc 72 4 R_CALLARM64 0 y6
reloc 88 4 R_CALLARM64 0 y7
pcln y13 y14 y15 y16 y8,y9,y10,y11,y12 y2,y3,_,_,_,y4,y5
usedfiles 1
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y8 SRODATA 11 1 28000 0001010202110103020500 0
data y9 SRODATA 7 1 28000 00120402030800 0
data y10 SRODATA 0 1 28000 - 0
data y11 SRODATA 5 1 28000 0006041600 0
data y12 SRODATA 6 1 28000 0012c0290a00 0
data y13 SRODATA 11 1 28000 0204200d1f0120021f0800 0
data y14 SRODATA 3 1 28000 041c00 0
data y15 SRODATA 14 1 28000 d601060206020202040302010800 0
data y16 SRODATA 3 1 28000 001c00 0
end
dwarf
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
sym y20 "go:info.regexp.(*queueOnePass).next$abstract" 0
sym y21 "" 0
sym y22 "go:info.*regexp.queueOnePass" 0
sym y23 "go:info.uint32" 0
sym y24 "type:uint32" 0
dwfn y17 y18 y19 y20 y21 "regexp.(*queueOnePass).next" 1:106 1 0 1 275
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y20 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "*regexp.queueOnePass" 0 0 1 p2:106:7:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uint32" 0 0 1 p2:106:32:0:0
var 0 0 "q" 5 1 0 0 0 8 y22 "regexp/onepass.go" 106 7 0 0 1 0 v0
var 1 0 "n" 5 1 1 0 0 0 y23 "regexp/onepass.go" 106 32 0 1 1 0 -
scope 0 0 - 0,1
dieref y17 3 y20 0
dieref y17 5 y20 1
dieoff y20 0:32,1:40
data y17 SDWARFFCN 26 0 0 0600000000000070019c2900000000000000002a000000000000 6
reloc 0 0 R_USETYPE 0 y24
reloc 1 4 R_DWARFSECREF 0 y20
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y20
reloc 15 4 R_DWARFSECREF 0 y18
reloc 20 4 R_DWARFSECREF 0 y20
data y18 SDWARFLOC 9 0 0 01000004003c015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y19 SDWARFRANGE 0 0 0 - 0
data y21 SDWARFLINES 39 0 0 0009020000000000000000040203e400140a8788063706d8063706380637850637360220000101 1
reloc 3 8 R_ADDR 0 y1
data y20 SDWARFABSFCN 49 0 1 057265676578702e282a71756575654f6e6550617373292e6e65787400016a012271000000000000226e00010000000000 2
reloc 36 4 R_DWARFSECREF 0 y22
reloc 44 4 R_DWARFSECREF 0 y23
end
eof
"#

/-- The loaded `(*queueOnePass).next` (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG21` gives (`b1`: the no-code `v6`, `v1`; `v29`'s `LDP`, the no-code
`Select`s; `v13`'s `MOVWU`, `v15`'s `MOVD`, `v30`'s `CMP`, then `BHS`; `b2`; `b3`). -/
def tab : PcTab := [(1, [5, 5, 5, 7, 7, 7, 8, 9, 10]), (2, [11, 12, 13, 14, 15, 15]), (3, [16, 19])]

/-- The class table `checkG21` gives. -/
def kt : KTab := (match checkG21 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- The machine address of `heap 1` (`GenG12.ι`). -/
def A : BitVec 64 := 0x20000000000

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `2^41` and the PC table of `checkG21`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The receiver `q`: the start of the heap object `heap 1`. -/
def pB : Ptr := ⟨.heap 1, 0⟩

/-- The field `q.nextIndex` (`uint32` at offset 52) that `v13` loads. -/
def pQ : Ptr := ⟨.heap 1, 52⟩

/-- The bytes of `heap 1`: `nextIndex = 0xffff_fffe`, little-endian at offset 52, 0 elsewhere. -/
def byteH (i : Nat) : BitVec 8 := if i = 52 then 0xfe else if 52 < i ∧ i < 56 then 0xff else 0

/-- The Phase 1 memory before `v13`: `heap 1` a block of 56 bytes `byteH`. -/
def memH : Mem :=
  { blocks := #[(.heap 1, { data := Array.ofFn (n := 56) fun i => .b (byteH i.val) })],
    nextHeap := 2 }

/-- The machine memory before `v13`: the bytes of `heap 1` at `A`, 0 elsewhere. -/
def MH : Memory := fun y => if (y - A).toNat < 56 then byteH (y - A).toNat else 0

/-- The `runLoc` state before `v13`: `q` (`pB`) in `R0`, every other register `poison`, the
memory `memH`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := memH },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .ptr pB else .poison,
    flags := .poison, slots := [], mem := .mem memH }

/-- The machine before `v13`: `X0` the address `A` of `q`, the activation's `g` and `FP`, the PC
of `v13`, the memory `MH`. -/
def m0 : MState :=
  { x := fun k => if k = 0 then A else if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8
      else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 5, mem := MH }

/-- A shape other than a boolean. -/
def notBool : Ty → Bool
  | .bool => false
  | _ => true

theorem notBool_spec {t : Ty} (h : notBool t = true) : t ≠ .bool := by
  rintro rfl; cases h

/-- `0xffff_fffe` as a 32-bit word, the loaded bytes. -/
def wl : BitVec 32 := 0xfffffffe

/-- Its zero extension to 64 bits. -/
def wz : BitVec 64 := 0xfffffffe

/-- The register holds the 32-bit integer `wl`. -/
def isWl : Option Val → Bool
  | some (.int .w32 x) => decide (x = wl)
  | _ => false

theorem isWl_spec {o : Option Val} (h : isWl o = true) : o = some (.int .w32 wl) := by
  unfold isWl at h
  split at h
  · rw [of_decide_eq_true h]
  · cases h

/-- The register holds the 64-bit integer `wz`. -/
def isWz : Option Val → Bool
  | some (.int .w64 x) => decide (x = wz)
  | _ => false

theorem isWz_spec {o : Option Val} (h : isWz o = true) : o = some (.int .w64 wz) := by
  unfold isWz at h
  split at h
  · rw [of_decide_eq_true h]
  · cases h

/-- `v13`'s address in `s0`: `R0`'s pointer moved by 52 is `pQ`. -/
def addrIsQ (s : LocState) : Bool :=
  GenG1.okThen (s.read lc 6) fun x => decide (symAddr lc.ctx (val 13) x = some pQ)

theorem addrIsQ_spec {s : LocState} (h : addrIsQ s = true) :
    ∃ x, s.read lc 6 = .ok x ∧ symAddr lc.ctx (val 13) x = some pQ := by
  obtain ⟨x, hx, h1⟩ := GenG1.okThen_spec h
  exact ⟨x, hx, of_decide_eq_true h1⟩

/-- What compiled evaluation checks on `(*queueOnePass).next`: `checkG21` accepts it with `tab`
and `kt` and `checkG20` does not; it accesses no frame variable and has no home slot; `b1` holds
`v13` (`MOVWUload` of `v6`, not a boolean) at index 5 and `v15` (`MOVDreg`) at index 6, `R0` has
class 64 before `v13` and nothing is in the upper-bit table there; in `s0` `v13`'s address is
`pQ`, where `memH` reads 4 bytes; `stepLoc` runs `v13` from `s0` to `R3 = 0xffff_fffe` as a 32-bit
integer and then `v15` to `R4 = 0xffff_fffe` as a 64-bit integer, which `Ptr.ofAddr` reads as no
block's address; and the upper-bit table before `v15` says `R3` is zero-extended from 32 bits. -/
def gFacts : Bool :=
  (checkG21 lc ps bs g).toOption == some (tab, kt) && (checkG20 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 13).isSome && (lc.ctx.f.value? 15).isSome &&
    blk1.values[5]? == some 13 && blk1.values[6]? == some 15 &&
    (val 13).op == .ARM64MOVWUload && (val 15).op == .ARM64MOVDreg &&
    (val 13).args[0]? == some 6 && notBool (lc.ty (val 13).id) &&
    (kAt lc kt 1 blk1 5).get 0 == some 64 && uAt lc blk1 5 == none &&
    addrIsQ s0 && (memH.read pQ 4).isSome &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 13)) (fun s1 =>
      isWl s1.regs[3]? && GenG1.okThen (stepLoc GenG2.env lc s1 (val 15)) fun s2 =>
        isWz s2.regs[4]?) &&
    (Ptr.ofAddr wz).blk == .nil && uAt lc blk1 6 == some (3, 32, false)

theorem g21_facts : gFacts = true := by
  native_decide

/-- The facts of `g21_facts` as hypotheses. -/
theorem facts :
    checkG21 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 1 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 1 = some blk1 ∧ lc.ctx.f.value? 13 = some (val 13) ∧
      lc.ctx.f.value? 15 = some (val 15) ∧ blk1.values[5]? = some 13 ∧
      blk1.values[6]? = some 15 ∧ (val 13).op = .ARM64MOVWUload ∧ (val 15).op = .ARM64MOVDreg ∧
      (val 13).args[0]? = some 6 ∧ lc.ty (val 13).id ≠ .bool ∧
      (kAt lc kt 1 blk1 5).get 0 = some 64 ∧ uAt lc blk1 5 = none ∧
      addrIsQ s0 = true ∧ (memH.read pQ 4).isSome = true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 13)) (fun s1 =>
        isWl s1.regs[3]? && GenG1.okThen (stepLoc GenG2.env lc s1 (val 15)) fun s2 =>
          isWz s2.regs[4]?) = true ∧
      (Ptr.ofAddr wz).blk = .nil ∧ uAt lc blk1 6 = some (3, 32, false) := by
  have hf := g21_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hm1⟩, hb1s⟩, hv13s⟩, hv15s⟩, hi5⟩, hi6⟩,
    hop13⟩, hop15⟩, ha0⟩, hty⟩, hk0⟩, hu5⟩, hq⟩, hrd⟩, hrun⟩, hnil⟩, hu6⟩ := hf
  refine ⟨?_, hav, hsl, hm1, ?_, ?_, ?_, hi5, hi6, hop13, hop15, ha0, notBool_spec hty, hk0, hu5,
    hq, hrd, hrun, hnil, hu6⟩
  · revert hres; cases checkG21 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [blk1, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv13s
    simp [val, hv]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv15s
    simp [val, hv]

theorem g21Env (hc : checkG21 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG21_spec hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := GenG12.addrAgree
        glob := fun _ _ _ _ => rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG21_spec hc
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

theorem memH_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ memH.blocks) :
    b = .heap 1 ∧ al = { data := Array.ofFn (n := 56) fun i => .b (byteH i.val) } := by
  simpa [memH] using h

/-- `memH` injected into `MH` by `ι`: `heap 1`'s bytes at `A`. -/
theorem memInjH : MemInj GenG12.ι memH MH where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := memH_blocks h
    exact ⟨A, rfl, fun _ => by decide, by simp [A]⟩
  inj := by
    intro b al b' al' a a' h h' hne
    obtain ⟨rfl, -⟩ := memH_blocks h
    obtain ⟨rfl, -⟩ := memH_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    obtain ⟨rfl, rfl⟩ := memH_blocks h
    have ha' : a = A := by simp [GenG12.ι] at ha; exact ha.symm
    subst ha'
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    simp only [Array.size_ofFn] at hi
    have hd : (A + BitVec.ofNat 64 i - A).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    simp [ByteRel, MH, hd, hi]

theorem keysH : KeysNodup memH := by simp [KeysNodup, memH]

theorem sepH : SepFrom GenG12.ι (StkAt E) memH := by
  intro b al a h ha y hy
  obtain ⟨rfl, rfl⟩ := memH_blocks h
  have ha' : a = A := by simp [GenG12.ι] at ha; exact ha.symm
  subst ha'
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    have hA : A.toNat = 0x20000000000 := rfl
    rw [hsp] at h2
    simp only [hA, Array.size_ofFn]
    omega
  · cases hk

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .ptr pB) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 5 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact ⟨A, rfl, by decide⟩
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨memH, rfl, memInjH⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, MH, E, A]; decide,
    by simp only [MState.word, readMem, m0, MH, E, A]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g21Inv0 (h0 : (kAt lc kt 1 blk1 5).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk1 5) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, memH, rfl, keysH, sepH⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v13`, the load of `q.nextIndex`: its address is `pQ`, where `memH`
reads 4 bytes; it is no compare, subtraction, pair load, nil check, zeroing or register-index
load. -/
theorem pre13 (hop : (val 13).op = .ARM64MOVWUload) (ha0 : (val 13).args[0]? = some 6)
    (hty : lc.ty (val 13).id ≠ .bool) (hq : addrIsQ s0 = true)
    (hrd : (memH.read pQ 4).isSome = true) : G14Pre lc s0 (val 13) := by
  have hne : ∀ o : Op, o ≠ .ARM64MOVWUload → (val 13).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop)
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hrd
  obtain ⟨x0, hx0, hsym⟩ := addrIsQ_spec hq
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  rotate_left
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl
  intro as n sg hl a x ha hx
  rw [hop] at hl
  cases hl
  rw [ha0] at ha
  cases ha
  rw [hx0] at hx
  cases hx
  exact ⟨pQ, memH, bs, hsym, rfl, hbs, fun h => absurd h hty⟩

/-- The per-value premises of `v15`, `MOVDreg`: none apply. -/
theorem pre15 {s : LocState} (hop : (val 15).op = .ARM64MOVDreg) : G14Pre lc s (val 15) := by
  have hne : ∀ o : Op, o ≠ .ARM64MOVDreg → (val 15).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G21 on `(*queueOnePass).next`**: from the state before `v13` with `q` (`pB`) in `R0` and
`q.nextIndex = 0xffff_fffe` (`memH`, at `A` in `MH`), `g21_value` runs the zero-extending load
`MOVWU 52(R0), R3` (`v13`): `runLoc`'s `R3` holds the 32-bit integer `0xffff_fffe`, and the
upper-bit invariant `UOK` it establishes makes the machine's `X3` its zero extension; then
`g21_value` runs `MOVDreg` (`v15`, `MOVD R3, R4`) on that invariant: `runLoc`'s `R4` holds the
64-bit integer `0xffff_fffe` and the machine state, related to it before `v30` under an activation
extending `E`, has `X4 = 0x0000_0000_ffff_fffe`, which a sign extension
(`0xffff_ffff_ffff_fffe`) would not be. -/
theorem genG21_value_witness :
    ∃ s1 s2 E1 m1 E2 m2, stepLoc GenG2.env lc s0 (val 13) = .ok s1 ∧
      s1.regs[3]? = some (.int .w32 wl) ∧ stepLoc GenG2.env lc s1 (val 15) = .ok s2 ∧
      s2.regs[4]? = some (.int .w64 wz) ∧ E.Extends E1 ∧ E1.Extends E2 ∧
      G10Env lc g L ps 0 tab E2 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧ LocMatch E1 s1 1 6 m1 ∧
      m1.x 3 = wz ∧ PStar GenG2.H0 L ps.toList 0 m1 m2 ∧ LocMatch E2 s2 1 7 m2 ∧
      m2.x 4 = wz := by
  obtain ⟨hc, hav, hsl, hm1, hb, hv13, hv15, hi5, hi6, hop13, hop15, ha0, hty, hk0, hu5, hq, hrd,
    hrun, hnil, hu6⟩ := facts
  obtain ⟨s1, hs1, h2⟩ := GenG1.okThen_spec hrun
  rw [Bool.and_eq_true] at h2
  obtain ⟨hr1, h2⟩ := h2
  have hr1' : s1.regs[3]? = some (.int .w32 wl) := isWl_spec hr1
  obtain ⟨s2, hs2, hr2⟩ := GenG1.okThen_spec h2
  have hr2' : s2.regs[4]? = some (.int .w64 wz) := isWz_spec hr2
  have hE := g21Env hc hav hsl
  have hne13 : ∀ o : Op, o ≠ .ARM64MOVWUload → (val 13).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop13)
  have hne15 : ∀ o : Op, o ≠ .ARM64MOVDreg → (val 15).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop15)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', hinv1, hu1⟩ := g21_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm1 hb hi5 hv13 (by rw [hop13]; rfl) locMatch0 (g21Inv0 hk0) (by rw [hu5]; trivial)
    (pre13 hop13 ha0 hty hq hrd)
    (fun h => absurd h (hne13 _ (by decide))) (fun h => absurd h (hne13 _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop13]; rfl))
    (fun h => absurd h (hne13 _ (by decide))) (fun h => absurd h (hne13 _ (by decide)))
    (fun h => absurd h (hne13 _ (by decide))) hs1
  have hext : ExtOK (m1.x 3) 32 false := by
    rw [hu6] at hu1
    exact hu1 3 (by decide) rfl
  have hlo : (m1.x 3).setWidth 32 = wl := (hm1'.regs 3 _ hr1').1 3 rfl
  have hx3 : m1.x 3 = wz := by
    simp only [ExtOK, Bool.false_eq_true, ↓reduceIte] at hext
    rw [hext, hlo]
    decide
  obtain ⟨E2, m2, hx2, hE2, hp2, hm2', -, -⟩ := g21_value (H := GenG2.H0) (env := GenG2.env)
    hc hE1 hm1 hb hi6 hv15 (by rw [hop15]; rfl) hm1' hinv1 hu1 (pre15 hop15)
    (fun h => absurd h (hne15 _ (by decide))) (fun h => absurd h (hne15 _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop15]; rfl))
    (fun h => absurd h (hne15 _ (by decide))) (fun h => absurd h (hne15 _ (by decide)))
    (fun h => absurd h (hne15 _ (by decide))) hs2
  refine ⟨s1, s2, E1, m1, E2, m2, hs1, hr1', hs2, hr2', hx1, hx2, hE2, hp1, hm1', hx3, hp2, hm2',
    ?_⟩
  rcases (hm2'.regs 4 _ hr2').1 4 rfl with h | ⟨hn, -⟩
  · exact h
  · exact absurd hnil hn

end GoFV.Proof.Witness.GenG21
