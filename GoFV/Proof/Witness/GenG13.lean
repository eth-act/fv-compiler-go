import GoFV.Proof.Gen.G13
import GoFV.Proof.Witness.GenG12

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G13 of the genssa validator on `(*pageBits).clearAll`

`std/std/runtime/(*pageBits).clearAll,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain` (file names `%28%2ApageBits%29.clearAll,1.*`), embedded
verbatim (`fSsa`, `fProg`): `func (b *pageBits) clearAll() { *b = pageBits{} }`
(`runtime/mpallocbits.go`), `pageBits` a `[8]uint64`.

`checkG12` rejects it (`v27 = LoweredZero [64]`); `checkG13` accepts it with the PC table `tab`
and the class table `kt`. Block `b4`: `v5 = ArgIntReg` (`b`, `R0`), `v1 = InitMem`,
`v27 = LoweredZero [64] v5 v1`, `v29 = MakeResult v27`; `Ret`. Its Progs: `STP (ZR, ZR), 0(R0)`,
`… 16(R0)`, `… 32(R0)`, `… 48(R0)`, `RET`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g13_facts`),
`stepLoc` runs `v27` from the state after the entry values with `b` pointing to the heap object
`heap 1` of 64 bytes 7 (`mem7`), and the memory is then the object's 64 zero bytes (`memZ`). On a
framed activation with `G10Env` (as `GenG12`'s, `heap 1` injected at `2^41`) and the machine
memory holding the object's bytes there (`M7`), `g13_value` runs the four `STP`s and gives the
state before `v29`, related by `LocMatch`: the machine bytes of the object are then 0
(`genG13_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG13

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/(*pageBits).clearAll,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "(*pageBits).clearAll" 1 0 0
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
type t4 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t3 ARRAY 64 8 0 comparable,named "pageBits" "runtime.pageBits" t4 8
type t2 PTR 8 8 8 hasptr,direct,comparable "*pageBits" "*runtime.pageBits" t3
type t1 FUNC 8 8 8 hasptr,direct "method(*pageBits) func()" "method(*runtime.pageBits) func()" 1 0 0
field 0 "b" t2 ? 0
aux a2 sym "runtime.(*pageBits).clearAll" "runtime.(*pageBits).clearAll" 1 - 0 - - - - 0
posbase p56 "runtime/mpallocbits.go" 1 1 -1
aux a3 name "b" "b" PPARAM t2 0 1 used p56:94:7:0:0
aux a1 call "AuxCall{runtime.(*pageBits).clearAll}" a2 1 1 0 8 8 1 0
abiparam in 0 t2 a3 0 0
type t5 BOOL 1 1 0 comparable,named "bool" "bool"
type t6 INT8 1 1 0 comparable,named "int8" "int8"
type t7 INT16 2 2 0 comparable,named "int16" "int16"
type t8 INT32 4 4 0 comparable,named "int32" "int32"
type t9 INT64 8 8 0 comparable,named "int64" "int64"
type t10 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t11 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t12 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t13 INT 8 8 0 comparable,named "int" "int"
type t14 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t15 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t16 UINT 8 8 0 comparable,named "uint" "uint"
type t17 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t18 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t8
type t21 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t12
type t22 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t13
type t23 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t17
type t24 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t14
type t25 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t15
type t26 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t19
type t27 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t28 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t29 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t30 SSA ? ? ? - "mem" ""
type t31 SSA ? ? ? - "flags" ""
type t32 SSA ? ? ? - "void" ""
type t33 SSA 16 8 ? - "int128" ""
type t34 RESULTS ? ? ? - "mem" "" 1 t30
type t35 PTR 8 8 8 hasptr,direct,comparable "**pageBits" "**runtime.pageBits" t2
type t36 PTR 8 8 8 hasptr,direct,comparable "*uint64" "*uint64" t4
type t37 SLICE 24 8 8 hasptr "[]uint64" "[]uint64" t4
aux a5 sym "runtime.memclrNoHeapPointers" "runtime.memclrNoHeapPointers" 1 - 0 - - - - 0
aux a4 call "AuxCall{runtime.memclrNoHeapPointers}" a5 1 2 0 8 16 2 0
abiparam in 0 t29 - 0 0
abiparam in 1 t17 - 1 8
slot s1 a3 t2 0 - 0
f b1 t1 a1 29 5
typs Bool=t5,Int8=t6,Int16=t7,Int32=t8,Int64=t9,UInt8=t10,UInt16=t11,UInt32=t12,UInt64=t4,Int=t13,Float32=t14,Float64=t15,UInt=t16,Uintptr=t17,String=t18,BytePtr=t19,Int32Ptr=t20,UInt32Ptr=t21,IntPtr=t22,UintptrPtr=t23,Float32Ptr=t24,Float64Ptr=t25,BytePtrPtr=t26,Complex64=t27,Complex128=t28,UnsafePtr=t29,Mem=t30,Flags=t31,Void=t32,Int128=t33,ResultMem=t34
b b1 If p56:95:9:0:0 1 0 - v10 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:0:0 1 v5,v1
v v7 Copy t36 0 - p56:95:9:2:0 1 v6
v v8 Const64 t13 8 - p0:0:0:0:0 4 -
v v9 Const64 t13 0 - p0:0:0:0:0 5 -
v v10 IsSliceInBounds t5 0 - p56:95:9:0:0 1 v9,v8
b b2 If p56:95:7:0:0 0 0 - v16 b5:0,b4:0 b1:0
v v13 Sub64 t13 0 - p56:95:9:0:0 2 v8,v9
v v14 SliceMake t37 0 - p56:95:9:0:0 2 v7,v13,v13
v v15 SliceLen t13 0 - p56:95:7:0:0 2 v14
v v16 Neq64 t5 0 - p56:95:7:0:0 1 v15,v9
b b3 Exit p56:95:9:0:0 0 0 - v12 - b1:1
v v11 Copy t30 0 - p56:95:9:2:0 1 v1
v v12 PanicBounds t30 6 - p56:95:9:0:0 1 v9,v8,v11
b b4 Ret p56:96:1:0:0 0 0 - v29 - b2:1,b5:0
v v28 Phi t30 0 - p56:96:1:0:0 1 v1,v27
v v29 MakeResult t34 0 - p56:96:1:0:0 1 v28
b b5 Plain p56:95:7:0:0 0 0 - - b4:1 b2:0
v v17 Copy t37 0 - p56:95:7:2:0 2 v14
v v18 SliceLen t13 0 - p56:95:7:0:0 0 v17
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v17
v v20 PtrIndex t36 0 - p56:95:7:0:0 1 v19,v9
v v21 Copy t29 0 - p56:95:7:2:0 1 v20
v v22 Copy t13 0 - p56:95:7:2:0 1 v15
v v23 Mul64 t13 0 - p56:95:7:0:0 1 v22,v8
v v24 Copy t17 0 - p56:95:7:2:0 1 v23
v v25 Copy t30 0 - p56:95:7:2:0 1 v1
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v21,v24,v25
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,8=v8
freev -
freeb -
dcllen 5
end
pass 1 "number lines"
f b1 t1 a1 29 5
b b1 If p56:95:9:0:0 1 0 - v10 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v7 Copy t36 0 - p56:95:9:2:0 1 v6
v v8 Const64 t13 8 - p0:0:0:0:0 4 -
v v9 Const64 t13 0 - p0:0:0:0:0 5 -
v v10 IsSliceInBounds t5 0 - p56:95:9:0:0 1 v9,v8
b b2 If p56:95:7:0:0 0 0 - v16 b5:0,b4:0 b1:0
v v13 Sub64 t13 0 - p56:95:9:0:0 2 v8,v9
v v14 SliceMake t37 0 - p56:95:9:0:0 2 v7,v13,v13
v v15 SliceLen t13 0 - p56:95:7:0:0 2 v14
v v16 Neq64 t5 0 - p56:95:7:0:0 1 v15,v9
b b3 Exit p56:95:9:0:0 0 0 - v12 - b1:1
v v11 Copy t30 0 - p56:95:9:2:0 1 v1
v v12 PanicBounds t30 6 - p56:95:9:0:0 1 v9,v8,v11
b b4 Ret p56:96:1:0:0 0 0 - v29 - b2:1,b5:0
v v28 Phi t30 0 - p56:96:1:0:0 1 v1,v27
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v28
b b5 Plain p56:95:7:0:0 0 0 - - b4:1 b2:0
v v17 Copy t37 0 - p56:95:7:2:0 2 v14
v v18 SliceLen t13 0 - p56:95:7:0:0 0 v17
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v17
v v20 PtrIndex t36 0 - p56:95:7:0:0 1 v19,v9
v v21 Copy t29 0 - p56:95:7:2:0 1 v20
v v22 Copy t13 0 - p56:95:7:2:0 1 v15
v v23 Mul64 t13 0 - p56:95:7:0:0 1 v22,v8
v v24 Copy t17 0 - p56:95:7:2:0 1 v23
v v25 Copy t30 0 - p56:95:7:2:0 1 v1
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v21,v24,v25
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,8=v8
freev -
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 56:95:96
dcllen 5
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 29 5
b b1 If p56:95:9:0:0 1 0 - v10 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 7 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 2 v5,v1
v v7 Copy t36 0 - p56:95:9:2:0 0 v6
v v8 Const64 t13 8 - p0:0:0:0:0 4 -
v v9 Const64 t13 0 - p0:0:0:0:0 5 -
v v10 IsSliceInBounds t5 0 - p56:95:9:0:0 1 v9,v8
b b2 If p56:95:7:0:0 0 0 - v16 b5:0,b4:0 b1:0
v v13 Sub64 t13 0 - p56:95:9:0:0 2 v8,v9
v v14 SliceMake t37 0 - p56:95:9:0:0 4 v6,v13,v13
v v15 SliceLen t13 0 - p56:95:7:0:0 3 v14
v v16 Neq64 t5 0 - p56:95:7:0:0 1 v15,v9
b b3 Exit p56:95:9:0:0 0 0 - v12 - b1:1
v v11 Copy t30 0 - p56:95:9:2:0 0 v1
v v12 PanicBounds t30 6 - p56:95:9:0:0 1 v9,v8,v1
b b4 Ret p56:96:1:0:0 0 0 - v29 - b2:1,b5:0
v v28 Phi t30 0 - p56:96:1:0:0 1 v1,v27
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v28
b b5 Plain p56:95:7:0:0 0 0 - - b4:1 b2:0
v v17 Copy t37 0 - p56:95:7:2:0 0 v14
v v18 SliceLen t13 0 - p56:95:7:0:0 0 v14
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v20 PtrIndex t36 0 - p56:95:7:0:0 2 v19,v9
v v21 Copy t29 0 - p56:95:7:2:0 0 v20
v v22 Copy t13 0 - p56:95:7:2:0 0 v15
v v23 Mul64 t13 0 - p56:95:7:0:0 2 v15,v8
v v24 Copy t17 0 - p56:95:7:2:0 0 v23
v v25 Copy t30 0 - p56:95:7:2:0 0 v1
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v20,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,8=v8
freev -
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 56:95:96
dcllen 5
end
pass 3 "early deadcode"
f b1 t1 a1 29 5
b b1 If p56:95:9:0:0 1 0 - v10 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v8 Const64 t13 8 - p0:0:0:0:0 4 -
v v9 Const64 t13 0 - p0:0:0:0:0 5 -
v v10 IsSliceInBounds t5 0 - p56:95:9:0:0 1 v9,v8
b b2 If p56:95:7:0:0 0 0 - v16 b5:0,b4:0 b1:0
v v13 Sub64 t13 0 - p56:95:9:0:0 2 v8,v9
v v14 SliceMake t37 0 - p56:95:9:0:0 2 v6,v13,v13
v v15 SliceLen t13 0 - p56:95:7:0:0 2 v14
v v16 Neq64 t5 0 - p56:95:7:0:0 1 v15,v9
b b3 Exit p56:95:9:0:0 0 0 - v12 - b1:1
v v12 PanicBounds t30 6 - p56:95:9:0:0 1 v9,v8,v1
b b4 Ret p56:96:1:0:0 0 0 - v29 - b2:1,b5:0
v v28 Phi t30 0 - p56:96:1:0:0 1 v1,v27
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v28
b b5 Plain p56:95:7:0:0 0 0 - - b4:1 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v20 PtrIndex t36 0 - p56:95:7:0:0 1 v19,v9
v v23 Mul64 t13 0 - p56:95:7:0:0 1 v15,v8
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v20,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,8=v8
freev v25,v24,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 56:95:96
dcllen 5
end
pass 4 "short circuit"
f b1 t1 a1 29 5
b b1 If p56:95:9:0:0 1 0 - v10 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v8 Const64 t13 8 - p0:0:0:0:0 4 -
v v9 Const64 t13 0 - p0:0:0:0:0 5 -
v v10 IsSliceInBounds t5 0 - p56:95:9:0:0 1 v9,v8
b b2 If p56:95:7:0:0 0 0 - v16 b5:0,b4:0 b1:0
v v13 Sub64 t13 0 - p56:95:9:0:0 2 v8,v9
v v14 SliceMake t37 0 - p56:95:9:0:0 2 v6,v13,v13
v v15 SliceLen t13 0 - p56:95:7:0:0 2 v14
v v16 Neq64 t5 0 - p56:95:7:0:0 1 v15,v9
b b3 Exit p56:95:9:0:0 0 0 - v12 - b1:1
v v12 PanicBounds t30 6 - p56:95:9:0:0 1 v9,v8,v1
b b4 Ret p56:96:1:0:0 0 0 - v29 - b2:1,b5:0
v v28 Phi t30 0 - p56:96:1:0:0 1 v1,v27
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v28
b b5 Plain p56:95:7:0:0 0 0 - - b4:1 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v20 PtrIndex t36 0 - p56:95:7:0:0 1 v19,v9
v v23 Mul64 t13 0 - p56:95:7:0:0 1 v15,v8
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v20,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,8=v8
freev v25,v24,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 56:95:96
dcllen 5
end
pass 5 "decompose user"
f b1 t1 a1 29 5
b b1 If p56:95:9:0:0 1 0 - v10 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v8 Const64 t13 8 - p0:0:0:0:0 4 -
v v9 Const64 t13 0 - p0:0:0:0:0 5 -
v v10 IsSliceInBounds t5 0 - p56:95:9:0:0 1 v9,v8
b b2 If p56:95:7:0:0 0 0 - v16 b5:0,b4:0 b1:0
v v13 Sub64 t13 0 - p56:95:9:0:0 2 v8,v9
v v14 SliceMake t37 0 - p56:95:9:0:0 2 v6,v13,v13
v v15 SliceLen t13 0 - p56:95:7:0:0 2 v14
v v16 Neq64 t5 0 - p56:95:7:0:0 1 v15,v9
b b3 Exit p56:95:9:0:0 0 0 - v12 - b1:1
v v12 PanicBounds t30 6 - p56:95:9:0:0 1 v9,v8,v1
b b4 Ret p56:96:1:0:0 0 0 - v29 - b2:1,b5:0
v v28 Phi t30 0 - p56:96:1:0:0 1 v1,v27
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v28
b b5 Plain p56:95:7:0:0 0 0 - - b4:1 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v20 PtrIndex t36 0 - p56:95:7:0:0 1 v19,v9
v v23 Mul64 t13 0 - p56:95:7:0:0 1 v15,v8
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v20,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,8=v8
freev v25,v24,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 56:95:96
dcllen 5
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 29 5
b b1 If p56:95:9:0:0 1 0 - v10 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v8 Const64 t13 8 - p0:0:0:0:0 4 -
v v9 Const64 t13 0 - p0:0:0:0:0 5 -
v v10 IsSliceInBounds t5 0 - p56:95:9:0:0 1 v9,v8
b b2 If p56:95:7:0:0 0 0 - v16 b5:0,b4:0 b1:0
v v13 Sub64 t13 0 - p56:95:9:0:0 2 v8,v9
v v14 SliceMake t37 0 - p56:95:9:0:0 2 v6,v13,v13
v v15 SliceLen t13 0 - p56:95:7:0:0 2 v14
v v16 Neq64 t5 0 - p56:95:7:0:0 1 v15,v9
b b3 Exit p56:95:9:0:0 0 0 - v12 - b1:1
v v12 PanicBounds t30 6 - p56:95:9:0:0 1 v9,v8,v1
b b4 Ret p56:96:1:0:0 0 0 - v29 - b2:1,b5:0
v v28 Phi t30 0 - p56:96:1:0:0 1 v1,v27
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v28
b b5 Plain p56:95:7:0:0 0 0 - - b4:1 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v20 PtrIndex t36 0 - p56:95:7:0:0 1 v19,v9
v v23 Mul64 t13 0 - p56:95:7:0:0 1 v15,v8
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v20,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,8=v8
freev v25,v24,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 56:95:96
dcllen 5
end
pass 7 "opt"
f b1 t1 a1 29 5
b b1 First p56:95:9:0:0 1 0 - - b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v8 Const64 t13 8 - p0:0:0:0:0 1 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
b b2 First p56:95:7:0:0 0 0 - - b5:0,b4:0 b1:0
v v13 Const64 t13 8 - p56:95:9:0:0 2 -
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v13,v13
b b3 Exit p56:95:9:0:0 0 0 - v12 - b1:1
v v12 PanicBounds t30 6 - p56:95:9:0:0 1 v9,v8,v1
b b4 Ret p56:96:1:0:0 0 0 - v29 - b2:1,b5:0
v v28 Phi t30 0 - p56:96:1:0:0 1 v1,v27
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v28
b b5 Plain p56:95:7:0:0 0 0 - - b4:1 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,8=v8
freev v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 56:95:96
dcllen 5
end
pass 8 "zero arg cse"
f b1 t1 a1 29 5
b b1 First p56:95:9:0:0 1 0 - - b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v8 Const64 t13 8 - p0:0:0:0:0 3 -
v v9 Const64 t13 0 - p0:0:0:0:0 1 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
b b2 First p56:95:7:0:0 0 0 - - b5:0,b4:0 b1:0
v v13 Const64 t13 8 - p56:95:9:0:0 0 -
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
b b3 Exit p56:95:9:0:0 0 0 - v12 - b1:1
v v12 PanicBounds t30 6 - p56:95:9:0:0 1 v9,v8,v1
b b4 Ret p56:96:1:0:0 0 0 - v29 - b2:1,b5:0
v v28 Phi t30 0 - p56:96:1:0:0 1 v1,v27
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v28
b b5 Plain p56:95:7:0:0 0 0 - - b4:1 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,8=v8
freev v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 56:95:96
dcllen 5
end
pass 9 "opt deadcode"
f b1 t1 a1 29 5
b b1 Plain p56:95:9:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
b b2 Plain p56:95:7:0:0 0 0 - - b5:0 b1:0
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
b b4 Ret p56:96:1:0:0 0 0 - v29 - b5:0
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 Plain p56:95:7:0:0 0 0 - - b4:0 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v28,v12,v13,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache linestarts 56:95:96
dcllen 5
end
pass 10 "generic cse"
f b1 t1 a1 29 5
b b1 Plain p56:95:9:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
b b2 Plain p56:95:7:0:0 0 0 - - b5:0 b1:0
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
b b4 Ret p56:96:1:0:0 0 0 - v29 - b5:0
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 Plain p56:95:7:0:0 0 0 - - b4:0 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v28,v12,v13,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b5,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b5:-:-:11:14,b5:b2:b4:-:8:17
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 11 "phiopt"
f b1 t1 a1 29 5
b b1 Plain p56:95:9:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
b b2 Plain p56:95:7:0:0 0 0 - - b5:0 b1:0
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
b b4 Ret p56:96:1:0:0 0 0 - v29 - b5:0
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 Plain p56:95:7:0:0 0 0 - - b4:0 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v28,v12,v13,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b5,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b5:-:-:11:14,b5:b2:b4:-:8:17
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 12 "gcse deadcode"
f b1 t1 a1 29 5
b b1 Plain p56:95:9:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
b b2 Plain p56:95:7:0:0 0 0 - - b5:0 b1:0
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
b b4 Ret p56:96:1:0:0 0 0 - v29 - b5:0
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 Plain p56:95:7:0:0 0 0 - - b4:0 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v28,v12,v13,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b5,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b5:-:-:11:14,b5:b2:b4:-:8:17
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 13 "nilcheckelim"
f b1 t1 a1 29 5
b b1 Plain p56:95:9:0:0 0 0 - - b2:0 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
b b2 Plain p56:95:7:0:0 0 0 - - b5:0 b1:0
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
b b4 Ret p56:96:1:0:0 0 0 - v29 - b5:0
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 Plain p56:95:7:0:0 0 0 - - b4:0 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v28,v12,v13,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b5,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b5:-:-:11:14,b5:b2:b4:-:8:17
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 14 "prove"
f b1 t1 a1 29 5
b b1 Plain p56:95:9:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
b b2 Plain p56:95:7:0:0 0 0 - - b5:0 b1:0
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
b b4 Ret p56:96:1:0:0 0 0 - v29 - b5:0
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 Plain p56:95:7:0:0 0 0 - - b4:0 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v28,v12,v13,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b5,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b5:-:-:11:14,b5:b2:b4:-:8:17
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 15 "divisible"
f b1 t1 a1 29 5
b b1 Plain p56:95:9:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
b b2 Plain p56:95:7:0:0 0 0 - - b5:0 b1:0
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
b b4 Ret p56:96:1:0:0 0 0 - v29 - b5:0
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 Plain p56:95:7:0:0 0 0 - - b4:0 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v28,v12,v13,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b5,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b5:-:-:11:14,b5:b2:b4:-:8:17
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 16 "divmod"
f b1 t1 a1 29 5
b b1 Plain p56:95:9:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
b b2 Plain p56:95:7:0:0 0 0 - - b5:0 b1:0
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
b b4 Ret p56:96:1:0:0 0 0 - v29 - b5:0
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 Plain p56:95:7:0:0 0 0 - - b4:0 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v28,v12,v13,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b5,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b5:-:-:11:14,b5:b2:b4:-:8:17
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 17 "middle opt"
f b1 t1 a1 29 5
b b1 Plain p56:95:9:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
b b2 Plain p56:95:7:0:0 0 0 - - b5:0 b1:0
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
b b4 Ret p56:96:1:0:0 0 0 - v29 - b5:0
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 Plain p56:95:7:0:0 0 0 - - b4:0 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v28,v12,v13,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b5,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b5:-:-:11:14,b5:b2:b4:-:8:17
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 18 "known bits"
f b1 t1 a1 29 5
b b1 Plain p56:95:9:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
b b2 Plain p56:95:7:0:0 0 0 - - b5:0 b1:0
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
b b4 Ret p56:96:1:0:0 0 0 - v29 - b5:0
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 Plain p56:95:7:0:0 0 0 - - b4:0 b2:0
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v28,v12,v13,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b5,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b5:-:-:11:14,b5:b2:b4:-:8:17
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 19 "early fuse"
f b4 t1 a1 29 5
b b1 BlockInvalid p56:95:9:0:0 0 0 - - - -
b b2 BlockInvalid p56:95:7:0:0 0 0 - - - -
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p56:94:6:2:0 1 -
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v26 StaticLECall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 BlockInvalid p56:95:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v28,v12,v13,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 20 "expand calls"
aux a6 nameoff "b+0" a3 0
f b4 t1 a1 29 5
b b1 BlockInvalid p56:95:9:0:0 0 0 - - - -
b b2 BlockInvalid p56:95:7:0:0 0 0 - - - -
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v14 SliceMake t37 0 - p56:95:9:0:0 1 v6,v8,v8
v v19 SlicePtr t36 0 - p56:95:7:0:0 1 v14
v v26 StaticCall t34 16 a4 p56:95:7:0:0 1 v19,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
v v28 SB t17 0 - p0:0:0:0:0 0 -
v v12 SP t17 0 - p0:0:0:0:0 1 -
v v13 OffPtr t35 0 - p0:0:0:0:0 0 v12
b b5 BlockInvalid p56:95:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v13,8=v8
freev v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 21 "decompose builtin"
f b4 t1 a1 29 5
b b1 BlockInvalid p56:95:9:0:0 0 0 - - - -
b b2 BlockInvalid p56:95:7:0:0 0 0 - - - -
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 2 v5,v1
v v14 SliceMake t37 0 - p56:95:9:0:0 0 v6,v8,v8
v v26 StaticCall t34 16 a4 p56:95:7:0:0 1 v6,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
v v28 SB t17 0 - p0:0:0:0:0 0 -
v v12 SP t17 0 - p0:0:0:0:0 1 -
v v13 OffPtr t35 0 - p0:0:0:0:0 0 v12
b b5 BlockInvalid p56:95:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v13,8=v8
freev v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 22 "softfloat"
f b4 t1 a1 29 5
b b1 BlockInvalid p56:95:9:0:0 0 0 - - - -
b b2 BlockInvalid p56:95:7:0:0 0 0 - - - -
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 2 v5,v1
v v14 SliceMake t37 0 - p56:95:9:0:0 0 v6,v8,v8
v v26 StaticCall t34 16 a4 p56:95:7:0:0 1 v6,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
v v28 SB t17 0 - p0:0:0:0:0 0 -
v v12 SP t17 0 - p0:0:0:0:0 1 -
v v13 OffPtr t35 0 - p0:0:0:0:0 0 v12
b b5 BlockInvalid p56:95:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v13,8=v8
freev v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 23 "branchelim"
f b4 t1 a1 29 5
b b1 BlockInvalid p56:95:9:0:0 0 0 - - - -
b b2 BlockInvalid p56:95:7:0:0 0 0 - - - -
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v8 Const64 t13 8 - p0:0:0:0:0 2 -
v v23 Const64 t13 64 - p56:95:7:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 2 v5,v1
v v14 SliceMake t37 0 - p56:95:9:0:0 0 v6,v8,v8
v v26 StaticCall t34 16 a4 p56:95:7:0:0 1 v6,v23,v1
v v27 SelectN t30 0 - p56:95:7:0:0 1 v26
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
v v28 SB t17 0 - p0:0:0:0:0 0 -
v v12 SP t17 0 - p0:0:0:0:0 1 -
v v13 OffPtr t35 0 - p0:0:0:0:0 0 v12
b b5 BlockInvalid p56:95:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v13,8=v8
freev v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 24 "late opt"
aux a7 type "uint8" t10
f b4 t1 a1 29 5
b b1 BlockInvalid p56:95:9:0:0 0 0 - - - -
b b2 BlockInvalid p56:95:7:0:0 0 0 - - - -
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 Zero t30 64 a7 p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 BlockInvalid p56:95:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 25 "dead auto elim"
f b4 t1 a1 29 5
b b1 BlockInvalid p56:95:9:0:0 0 0 - - - -
b b2 BlockInvalid p56:95:7:0:0 0 0 - - - -
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 Zero t30 64 a7 p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 BlockInvalid p56:95:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 26 "sccp"
f b4 t1 a1 29 5
b b1 BlockInvalid p56:95:9:0:0 0 0 - - - -
b b2 BlockInvalid p56:95:7:0:0 0 0 - - - -
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 Zero t30 64 a7 p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
b b5 BlockInvalid p56:95:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 27 "generic deadcode"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 Zero t30 64 a7 p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 28 "late fuse"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 Zero t30 64 a7 p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 29 "check bce"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 Zero t30 64 a7 p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 30 "dse"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 Zero t30 64 a7 p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 31 "memcombine"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 Zero t30 64 a7 p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 32 "writebarrier"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 NilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 Zero t30 64 a7 p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 33 "lower"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 34 "addressing modes"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 35 "late lower"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 36 "pair"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 37 "lowered deadcode for cse"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache auxmap a3:1,-:2
cache linestarts 56:95:96
dcllen 5
end
pass 38 "lowered cse"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
dcllen 5
end
pass 39 "elim unread autos"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
dcllen 5
end
pass 40 "tighten tuple selectors"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
dcllen 5
end
pass 41 "lowered deadcode"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
dcllen 5
end
pass 42 "checkLower"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
dcllen 5
end
pass 43 "loop invariant"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
dcllen 5
end
pass 44 "late phielim and copyelim"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
dcllen 5
end
pass 45 "tighten"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 6 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
dcllen 5
end
pass 46 "late deadcode"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 6 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
dcllen 5
end
pass 47 "critical"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 6 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
dcllen 5
end
pass 48 "phi tighten"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 6 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
dcllen 5
end
pass 49 "likelyadjust"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 6 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
dcllen 5
end
pass 50 "layout"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p56:95:9:1:0 1 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v6,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 6 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
fstate laidout
dcllen 5
end
pass 51 "schedule"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v6 ARM64LoweredNilCheck t32 0 - p56:95:9:1:0 0 v5,v1
v v27 ARM64LoweredZero t30 64 - p56:95:7:0:0 1 v5,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 6 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
fstate scheduled,laidout
dcllen 5
end
pass 52 "late nilcheck"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v27 ARM64LoweredZero t30 64 - p56:95:7:1:0 1 v5,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 6 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
fstate scheduled,laidout
dcllen 5
end
pass 53 "flagalloc"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v27 ARM64LoweredZero t30 64 - p56:95:7:1:0 1 v5,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v12,v28,v26,v14,v23,v8,v19,v9,v24,v25,v20,v16,v15,v10,v22,v21,v18,v17,v11,v7,v4,v3,v2
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 6 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
fstate scheduled,laidout
dcllen 5
end
pass 54 "regalloc"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v27 ARM64LoweredZero t30 64 - p56:95:7:1:0 1 v5,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v28
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 6 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
fstate scheduled,laidout
regalloc 6 v5:R0
dcllen 5
end
pass 55 "loop rotate"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v27 ARM64LoweredZero t30 64 - p56:95:7:1:0 1 v5,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v28
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 6 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
fstate scheduled,laidout
regalloc 6 v5:R0
dcllen 5
end
pass 56 "trim"
f b4 t1 a1 29 5
b b4 Ret p56:96:1:0:0 0 0 - v29 - -
v v5 ArgIntReg t2 0 a6 p56:96:1:0:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v27 ARM64LoweredZero t30 64 - p56:95:7:1:0 1 v5,v1
v v29 MakeResult t34 0 - p56:96:1:1:0 1 v27
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v28
freeb b5,b2,b1,b3
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 6 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 56:95:96
fstate scheduled,laidout
regalloc 6 v5:R0
dcllen 5
end
frontend
end
ptrcache t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t23,t26,t27,t28,t29,t37
typelink t30=t34
typeorder t6,t10,t7,t11,t8,t12,t9,t4,t13,t16,t17,t27,t28,t14,t15,t5,t19,t20,t21,t36,t22,t23,t24,t25,t26,t35,t2,t1,t37,t3,t18,t29,t30,t32,t31,t33,t34
eof
"#

/-- `std/std/runtime/(*pageBits).clearAll,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "(*pageBits).clearAll" 1
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
type t1 8 8 8 1 01 "*pageBits"
name n1 "b" PPARAM t1 1 "runtime.b" 0 a3
type t2 24 8 8 1 01 "[]uint64"
name n2 ".autotmp_1" PAUTO t2 3 "runtime..autotmp_1" 0 -
type t3 8 8 0 0 - "int"
name n3 ".autotmp_2" PAUTO t3 3 "runtime..autotmp_2" 0 -
type t4 8 8 8 1 01 "unsafe.Pointer"
name n4 ".autotmp_3" PAUTO t4 3 "runtime..autotmp_3" 0 -
type t5 8 8 0 0 - "uintptr"
name n5 ".autotmp_4" PAUTO t5 3 "runtime..autotmp_4" 0 -
in n1 0 used
in n2 0 used,autotmp
in n3 0 used,autotmp
in n4 0 used,autotmp
in n5 0 used,autotmp
out n1 0 used
opt n2 0 autotmp
opt n4 0 autotmp
opt n3 0 autotmp
opt n5 0 autotmp
stack 0 0 8
end
genin
posbase p56 "runtime/mpallocbits.go" 1 1 -1 55 "runtime/mpallocbits.go" "runtime/mpallocbits.go" 1 1
sym y1 "runtime.(*pageBits).clearAll" 1
curfn p56:94:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 94 201080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.(*pageBits).clearAll.arginfo1" 0
sym y5 "runtime.(*pageBits).clearAll.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p56:94:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p56:94:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p56:94:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p56:94:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p56:94:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p56:94:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p56:95:7:1:0
p 7 7 0 0 0 - STP 0 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 0 0 p56:95:7:1:0
p 8 8 0 0 0 - STP 0 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/16/-/- 0 0 p56:95:7:2:0
p 9 9 0 0 0 - STP 0 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/32/-/- 0 0 p56:95:7:2:0
p 10 10 0 0 0 - STP 0 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/48/-/- 0 0 p56:95:7:2:0
p 11 11 0 0 0 - RET 0 _ 0 - _ 0 0 p56:96:1:0:0
p 12 12 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 94 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 4
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 4:-10000:-1:-30000:50
dbgregout -
dbgpc -
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p56:94:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p56:94:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p56:94:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p56:94:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p56:94:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p56:94:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p56:95:7:1:0
p 7 0 0 0 436 - STP 0 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 0 0 p56:95:7:1:0
p 8 4 0 0 436 - STP 0 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/86/16/-/- 0 0 p56:95:7:2:0
p 9 8 0 0 436 - STP 0 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/86/32/-/- 0 0 p56:95:7:2:0
p 10 12 0 0 436 - STP 0 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/86/48/-/- 0 0 p56:95:7:2:0
p 11 16 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p56:96:1:0:0
fn y1 8 0 0 0 94 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 32 0 1f7c00a91f7c01a91f7c02a91f7c03a9c0035fd6000000000000000000000000 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y3,_,_,_,y4,y5
usedfiles 55
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y6 SRODATA 3 1 28000 010800 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 040800 0
data y10 SRODATA 3 1 28000 020800 0
data y11 SRODATA 3 1 28000 700800 0
data y12 SRODATA 6 1 28000 c00104020400 0
data y13 SRODATA 3 1 28000 000800 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.runtime.(*pageBits).clearAll$abstract" 0
sym y18 "" 0
sym y19 "go:info.*runtime.pageBits" 0
dwfn y14 y15 y16 y17 y18 "runtime.(*pageBits).clearAll" 55:94 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwprecursor y1 y17 n1
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime.pageBits" 0 0 1 p56:94:7:0:0
dwname n2 1 0 1 0 0 0 0 0 - - "[]uint64" 0 0 1 p56:95:9:0:0
dwname n4 1 0 1 0 0 0 0 0 - - "unsafe.Pointer" 0 0 1 p56:95:7:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p56:95:7:0:0
dwname n5 1 0 1 0 0 0 0 0 - - "uintptr" 0 0 1 p56:95:7:0:0
var 0 0 "b" 5 1 0 0 0 8 y19 "runtime/mpallocbits.go" 94 7 0 0 1 0 v0
scope 0 0 - 0
dieref y14 2 y17 0
dieoff y17 0:33
data y14 SDWARFFCN 20 0 0 0600000000000020019c29000000000000000000 4
reloc 1 4 R_DWARFSECREF 0 y17
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y17
reloc 15 4 R_DWARFSECREF 0 y15
data y15 SDWARFLOC 9 0 0 010000040020015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y18 SDWARFLINES 26 0 0 0009020000000000000000043803d90014063706880210000101 1
reloc 3 8 R_ADDR 0 y1
data y17 SDWARFABSFCN 42 0 1 0572756e74696d652e282a7061676542697473292e636c656172416c6c00015e01226200000000000000 1
reloc 37 4 R_DWARFSECREF 0 y19
end
eof
"#

/-- The loaded `(*pageBits).clearAll` (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG13` gives (block `b4`: `v27`'s first `STP` after the no-op Progs from 5,
then `RET`). -/
def tab : PcTab := [(4, [5, 5, 5, 11, 11])]

/-- The class table `checkG13` gives: nothing known at the entry `b4`. -/
def kt : KTab := [(4, KMap.bot)]

def blk4 : Block := (lc.ctx.f.block? 4).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- `ι`: as `GenG12.ι`, the heap object `heap 1` at `2^41`. -/
def ι : Blk → Option (BitVec 64) := GenG12.ι

/-- The machine address of `heap 1`. -/
def A : BitVec 64 := 0x20000000000

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `2^41` and the PC table of `checkG13`. -/
def E : MatchEnv :=
  { lc, ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The argument `b`: the start of the heap object `heap 1`. -/
def pB : Ptr := ⟨.heap 1, 0⟩

/-- The Phase 1 memory before `v27`: `heap 1` a writable block of 64 bytes 7. -/
def mem7 : Mem := { blocks := #[(.heap 1, { data := Array.replicate 64 (.b 7) })], nextHeap := 2 }

/-- The Phase 1 memory after `v27`: `heap 1` holds 64 zero bytes. -/
def memZ : Mem := { blocks := #[(.heap 1, { data := Array.replicate 64 (.b 0) })], nextHeap := 2 }

/-- The machine memory before `v27`: the 64 bytes 7 of `heap 1` at `A`, 0 elsewhere. -/
def M7 : Memory := fun y => if (y - A).toNat < 64 then 7 else 0

/-- The `runLoc` state after the entry values: `b` in `R0`, every other register `poison`, the
memory `mem7`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem7 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .ptr pB else .poison,
    flags := .poison, slots := [], mem := .mem mem7 }

/-- The machine before `v27`: `X0` the address `A` of `b`, the activation's `g` and `FP`, the PC
of `v27`, the memory `M7`. -/
def m0 : MState :=
  { x := fun k => if k = 0 then A else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 4 2, mem := M7 }

/-- A register content addressing `pB` (`R0` reads as the Phase 1 address of `pB`). -/
def isPB (x : Val) : Bool := Arm64.addr x 0 == some pB

theorem isPB_spec {x : Val} (h : isPB x = true) : Arm64.addr x 0 = some pB := by
  simpa [isPB] using h

/-- The memory is `memZ`. -/
def memIsZ (s : LocState) : Bool :=
  match s.mem with
  | .mem mm => decide (mm = memZ)
  | _ => false

theorem memIsZ_spec {s : LocState} (h : memIsZ s = true) : s.mem = .mem memZ := by
  unfold memIsZ at h
  split at h
  · rename_i mm hmm
    rw [hmm, of_decide_eq_true h]
  · cases h

/-- What compiled evaluation checks on `clearAll`: `checkG13` accepts it with `tab` and `kt` and
`checkG12` does not; it accesses no frame variable and has no home slot; `b4` holds `v27` at
index 2, a `LoweredZero [64]` of `v5`, and `R0` has class 64 before it; `v5` reads in `s0` as an
address of `pB`; writing 64 zero bytes at `pB` in `mem7` gives `memZ`; `stepLoc` runs `v27` from `s0` to the
memory `memZ`; and no 8 bytes of `memZ`'s block encode a pointer. -/
def gFacts : Bool :=
  (checkG13 lc ps bs g).toOption == some (tab, kt) && (checkG12 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 4 && (lc.ctx.f.block? 4).isSome &&
    (lc.ctx.f.value? 27).isSome && blk4.values[2]? == some 27 &&
    (val 27).op == .ARM64LoweredZero && (val 27).args[0]? == some 5 &&
    (val 27).auxInt.toInt.toNat == 64 && (kAt lc kt 4 blk4 2).get 0 == some 64 &&
    GenG1.okThen (s0.read lc 5) isPB &&
    decide (mem7.write pB (Array.replicate 64 (.b 0)) = some memZ) &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 27)) memIsZ &&
    (List.range 64).all fun o => ptrWordAt? (Array.replicate 64 (.b 0)) o == none

theorem g13_facts : gFacts = true := by
  native_decide

/-- The facts of `g13_facts` as hypotheses. -/
theorem facts :
    checkG13 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 4 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 4 = some blk4 ∧ lc.ctx.f.value? 27 = some (val 27) ∧
      blk4.values[2]? = some 27 ∧ (val 27).op = .ARM64LoweredZero ∧ (val 27).args[0]? = some 5 ∧
      (val 27).auxInt.toInt.toNat = 64 ∧ (kAt lc kt 4 blk4 2).get 0 = some 64 ∧
      GenG1.okThen (s0.read lc 5) isPB = true ∧
      mem7.write pB (Array.replicate 64 (.b 0)) = some memZ ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 27)) memIsZ = true ∧
      ∀ o, o < 64 → ptrWordAt? (Array.replicate 64 (.b 0)) o = none := by
  have hf := g13_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hm4⟩, hb4s⟩, hv27⟩, hi2⟩, hop⟩, ha0⟩, hn⟩, hk0⟩,
    hrd⟩, hwr⟩, hrun⟩, hpw⟩ := hf
  refine ⟨?_, hav, hsl, hm4, ?_, ?_, hi2, hop, ha0, hn, hk0, hrd, hwr, hrun, hpw⟩
  · revert hres; cases checkG13 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb4s
    simp [blk4, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv27
    simp [val, hv]

theorem g13Env (hc : checkG13 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG13_spec hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := GenG12.addrAgree
        glob := fun _ _ _ _ => rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG13_spec hc
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

theorem mem7_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ mem7.blocks) :
    b = .heap 1 ∧ al = { data := Array.replicate 64 (.b 7) } := by
  simpa [mem7] using h

/-- `mem7` injected into `M7` by `ι`: `heap 1`'s bytes 7 at `A`. -/
theorem memInj7 : MemInj ι mem7 M7 where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := mem7_blocks h
    exact ⟨A, rfl, fun _ => by decide, by simp [A]⟩
  inj := by
    intro b al b' al' a a' h h' hne
    obtain ⟨rfl, -⟩ := mem7_blocks h
    obtain ⟨rfl, -⟩ := mem7_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    obtain ⟨rfl, rfl⟩ := mem7_blocks h
    have ha' : a = A := by simp [ι, GenG12.ι] at ha; exact ha.symm
    subst ha'
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    simp only [Array.size_replicate] at hi
    have hd : (A + BitVec.ofNat 64 i - A).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    simp [ByteRel, M7, hd, hi]

theorem keys7 : KeysNodup mem7 := by simp [KeysNodup, mem7]

theorem sep7 : SepFrom ι (StkAt E) mem7 := by
  intro b al a h ha y hy
  obtain ⟨rfl, rfl⟩ := mem7_blocks h
  have ha' : a = A := by simp [ι, GenG12.ι] at ha; exact ha.symm
  subst ha'
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    have hA : A.toNat = 0x20000000000 := rfl
    rw [hsp] at h2
    simp only [hA, Array.size_replicate]
    omega
  · cases hk

theorem locMatch0 : LocMatch E s0 4 2 m0 where
  regs := by
    intro r v hv
    simp only [s0, Array.getElem?_ofFn] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · split at hv
        · subst hv
          rename_i h0
          subst h0
          simp only [objX?] at hk
          cases hk
          exact ⟨A, rfl, by decide⟩
        · subst hv; trivial
      · split at hv
        · rename_i h0; subst h0; simp [objV?] at hk
        · subst hv; trivial
    · cases hv
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem7, rfl, memInj7⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, M7, E, A]; decide,
    by simp only [MState.word, readMem, m0, M7, E, A]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g13Inv0 (h0 : (kAt lc kt 4 blk4 2).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 4 blk4 2) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem7, rfl, keys7, sep7⟩
    simp only [s0, Array.getElem?_ofFn] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      split at hv
      · rename_i h0'
        subst hv; subst h0'
        rw [h0] at hc; cases hc; rfl
      · subst hv; trivial
    · cases hv
  slots := by intro k v h; simp [s0] at h

theorem g7Pre_of {v : Value} (h1 : v.op ≠ .ARM64CMP) (h2 : v.op ≠ .ARM64CMPconst)
    (h3 : loadOp? v.op = none) (h4 : v.op ≠ .ARM64LDP) (h5 : v.op ≠ .ARM64SUB)
    (h6 : v.op ≠ .ARM64LoweredNilCheck) (s : LocState) : G7Pre lc s v :=
  ⟨⟨⟨fun h => by rcases h with h | h <;> contradiction,
    (fun _ _ _ hl => by rw [h3] at hl; cases hl), fun h => absurd h h5⟩, fun h => absurd h h4⟩,
    fun h => absurd h h6⟩

/-- `v27` zeroes the 64 bytes of `heap 1`, a valid write in `mem7`. -/
theorem zeroPre0 (ha0 : (val 27).args[0]? = some 5) (hn : (val 27).auxInt.toInt.toNat = 64)
    (hrd : GenG1.okThen (s0.read lc 5) isPB = true)
    (hwr : mem7.write pB (Array.replicate 64 (.b 0)) = some memZ) : ZeroPre lc s0 (val 27) := by
  intro _ a x ha hx
  rw [ha0] at ha
  cases ha
  obtain ⟨y, hy, hpb⟩ := GenG1.okThen_spec hrd
  rw [hx] at hy
  cases hy
  rw [hn]
  exact ⟨pB, mem7, memZ, isPB_spec hpb, rfl, hwr⟩

/-- **G13 on `clearAll`**: from the state after the entry values with `b` (`pB`) in `R0` and
`heap 1` 64 bytes 7 (`mem7`, at `A` in `M7`), `g13_value` runs the zeroing `v27` (the four
`STP (ZR, ZR)`) and gives the state before `v29`, with the memory `memZ` related to the machine's
under an activation that extends `E` and is a `G10Env`: the 64 machine bytes at `A` are then 0. -/
theorem genG13_value_witness :
    ∃ s1 E' m1, stepLoc GenG2.env lc s0 (val 27) = .ok s1 ∧ s1.mem = .mem memZ ∧
      E.Extends E' ∧ G10Env lc g L ps 0 tab E' ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E' s1 4 3 m1 ∧ G3Inv E' lc (kAt lc kt 4 blk4 3) s1 ∧
      ∀ i, i < 64 → m1.mem (A + BitVec.ofNat 64 i) = 0 := by
  obtain ⟨hc, hav, hsl, hm4, hb, hv27, hi2, hop, ha0, hn, hk0, hrd, hwr, hrun, hpw⟩ := facts
  obtain ⟨s1, hs1, hz⟩ := GenG1.okThen_spec hrun
  have hE := g13Env hc hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64LoweredZero → (val 27).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', hinv1⟩ := g13_value (H := GenG2.H0) (env := GenG2.env) hc
    hE hm4 hb hi2 hv27 (by rw [hop]; rfl) locMatch0 (g13Inv0 hk0)
    ⟨g7Pre_of (hne _ (by decide)) (hne _ (by decide)) (by rw [hop]; simp [loadOp?, narrowLoad?])
      (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide)) _, zeroPre0 ha0 hn hrd hwr⟩
    (fun h => absurd h (hne _ (by decide))) (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  refine ⟨s1, E1, m1, hs1, memIsZ_spec hz, hx1, hE1, hp1, hm1', hinv1, fun i hi => ?_⟩
  obtain ⟨mm, hmm, hMI⟩ := hm1'.mem
  rw [memIsZ_spec hz] at hmm
  cases hmm
  obtain ⟨W, hW⟩ := hMI.bytes
  have hA : E1.ι (.heap 1) = some A := hx1.2 _ _ rfl
  obtain ⟨hw, -, hby⟩ := hW (.heap 1) { data := Array.replicate 64 (.b 0) } A (by simp [memZ]) hA
  have hnw : ∀ o, ¬ W (.heap 1) o := by
    intro o ho
    obtain ⟨p, hp, -⟩ := hw o ho
    by_cases ho64 : o < 64
    · rw [hpw o ho64] at hp; cases hp
    · simp [ptrWordAt?] at hp; omega
  have := hby i (by simpa using hi) (fun o ho => absurd ho (hnw o))
  simp only [Array.getElem_replicate, ByteRel] at this
  exact this.symm

end GoFV.Proof.Witness.GenG13
