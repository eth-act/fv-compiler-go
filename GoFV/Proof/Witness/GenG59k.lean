import GoFV.Gen.Check58
import GoFV.Proof.Gen.G58
import GoFV.Proof.Witness.GenG2

/-!
# Witness: slice G59, group K (narrower register classes) on `math.lz`

`std/std/math/lz` (quick-v10, `func lz(u1, u2 uint64) (l int32)` of `math/fma.go`): `b2`
(`CLZ R0, R0` of `u1`: `v19`) branches to `b3` or to `b5` (`CLZ R1, R1` of `u2`, `ADD $64, R1, R0`:
`v9`); `b3` holds the 32-bit `Phi` `v27` of the 64-bit `v19` and `v9`, homed in `R0`, and returns
it (`v29 = MakeResult v27`, read at 32 bits). The class
table used to reject it (`v29: a register read at another class`: `R0` holds class 64 at the end
of both predecessors, and an edge had to keep each class). With `kNarrow` the table claims class
32 for `R0` at `b3` (`kPhis`), `kLe` accepts the edge from 64 and `checkG58` accepts `lz`.

From a state at `b5`'s jump whose `R0` holds the 64-bit `0xffffffff00000045`, `g58_term` (through
`CoreInv.monoW`) runs the jump to `b3`, related at the class table there (`R0` at 32 bits), and
`arg_rel` (through `valRel_retypeLW`) relates `v27`'s read, the low word `0x45`, to `X0`, whose
upper word stays `0xffffffff`.
-/

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG59k

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/math/lz,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "math"
func "lz" 1 0 0
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
type t2 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t3 INT32 4 4 0 comparable,named "int32" "int32"
type t1 FUNC 8 8 8 hasptr,direct "func(uint64, uint64) int32" "func(uint64, uint64) int32" 0 2 1
field 0 "u1" t2 ? 0
field 1 "u2" t2 ? 0
field 2 "l" t3 ? 0
aux a2 sym "math.lz" "math.lz" 1 - 0 - - - - 0
posbase p32 "math/fma.go" 1 1 -1
aux a3 name "u1" "u1" PPARAM t2 0 1 used p32:65:9:0:0
aux a4 name "u2" "u2" PPARAM t2 8 1 used p32:65:13:0:0
aux a5 name "l" "l" PPARAMOUT t3 0 1 used p32:65:25:0:0
aux a1 call "AuxCall{math.lz}" a2 1 2 1 8 16 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t2 a4 1 8
abiparam out 0 t3 a5 0 -1
type t4 BOOL 1 1 0 comparable,named "bool" "bool"
type t5 INT8 1 1 0 comparable,named "int8" "int8"
type t6 INT16 2 2 0 comparable,named "int16" "int16"
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
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t3
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
type t33 PTR 8 8 8 hasptr,direct,comparable "*uint64" "*uint64" t2
posbase p289 "math/bits/bits.go" 1 1 233
type t34 RESULTS ? ? ? - "int32,mem" "" 2 t3,t28
posbase p290 "math/bits/bits.go" 1 1 234
slot s1 a3 t2 0 - 0
slot s2 a4 t2 0 - 0
aux a6 name "bits.x" "x" PAUTO t2 0 1 used p289:37:21:0:0
slot s3 a6 t2 0 - 0
aux a7 name "~r0" "~r0" PAUTO t11 0 1 - p289:37:31:0:0
slot s4 a7 t11 0 - 0
aux a8 name "bits.x" "x" PAUTO t2 0 1 used p290:37:21:0:0
slot s5 a8 t2 0 - 0
aux a9 name "~r0" "~r0" PAUTO t11 0 1 - p290:37:31:0:0
slot s6 a9 t11 0 - 0
f b1 t1 a1 29 5
typs Bool=t4,Int8=t5,Int16=t6,Int32=t3,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t2,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Plain p32:66:31:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 6 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t18 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v9 Const32 t3 0 - p0:0:0:0:0 0 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:0:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
b b2 If p32:67:10:0:0 0 0 - v17 b4:0,b3:0 b1:0
v v14 Copy t11 0 - p32:66:31:2:0 1 v13
v v15 Trunc64to32 t3 0 - p32:66:31:0:0 3 v14
v v17 Eq32 t4 0 - p32:67:7:0:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v28 Phi t28 0 - p32:70:2:0:0 1 v1,v19
v v29 MakeResult t34 0 - p32:70:2:0:0 1 v27,v28
b b4 Plain p32:68:33:1:0 0 0 - - b5:0 b2:0
v v18 Copy t2 0 - p32:68:33:2:0 1 v8
v v19 Copy t28 0 - p32:68:33:2:0 2 v1
v v20 InlMark t30 234 - p32:68:33:1:0 0 v19
v v21 BitLen64 t11 0 - p290:37:54:0:0 1 v18
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b4:0
v v23 Copy t3 0 - p32:68:5:2:0 1 v15
v v24 Copy t11 0 - p32:68:33:2:0 1 v22
v v25 Trunc64to32 t3 0 - p32:68:33:0:0 1 v24
v v26 Add32 t3 0 - p32:68:5:0:0 1 v23,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8,v18
named s3 v7
named s4 v13,v14
named s5 v18
named s6 v22,v24
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 0=v9,64=v12,v16
freev -
freeb -
dcllen 8
end
pass 1 "number lines"
f b1 t1 a1 29 5
b b1 Plain p32:66:31:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 6 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t18 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v9 Const32 t3 0 - p0:0:0:0:0 0 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
b b2 If p32:67:10:0:0 0 0 - v17 b4:0,b3:0 b1:0
v v14 Copy t11 0 - p32:66:31:2:0 1 v13
v v15 Trunc64to32 t3 0 - p32:66:31:0:0 3 v14
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v28 Phi t28 0 - p32:70:2:0:0 1 v1,v19
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v28
b b4 Plain p32:68:33:1:0 0 0 - - b5:0 b2:0
v v18 Copy t2 0 - p32:68:33:2:0 1 v8
v v19 Copy t28 0 - p32:68:33:2:0 2 v1
v v20 InlMark t30 234 - p32:68:33:1:0 0 v19
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v18
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b4:0
v v23 Copy t3 0 - p32:68:5:2:0 1 v15
v v24 Copy t11 0 - p32:68:33:2:0 1 v22
v v25 Trunc64to32 t3 0 - p32:68:33:0:0 1 v24
v v26 Add32 t3 0 - p32:68:5:0:0 1 v23,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8,v18
named s3 v7
named s4 v13,v14
named s5 v18
named s6 v22,v24
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 0=v9,64=v12,v16
freev -
freeb -
cache postorder b3,b5,b4,b2,b1
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 29 5
b b1 Plain p32:66:31:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t18 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 2 -
v v9 Const32 t3 0 - p0:0:0:0:0 0 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 2 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
b b2 If p32:67:10:0:0 0 0 - v17 b4:0,b3:0 b1:0
v v14 Copy t11 0 - p32:66:31:2:0 0 v13
v v15 Trunc64to32 t3 0 - p32:66:31:0:0 4 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v28 Copy t28 0 - p32:70:2:0:0 0 v1
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b4 Plain p32:68:33:1:0 0 0 - - b5:0 b2:0
v v18 Copy t2 0 - p32:68:33:2:0 0 v8
v v19 Copy t28 0 - p32:68:33:2:0 0 v1
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 2 v12,v21
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b4:0
v v23 Copy t3 0 - p32:68:5:2:0 0 v15
v v24 Copy t11 0 - p32:68:33:2:0 0 v22
v v25 Trunc64to32 t3 0 - p32:68:33:0:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v15,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8,v8
named s3 v7
named s4 v13,v13
named s5 v8
named s6 v22,v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 0=v9,64=v12,v16
freev -
freeb -
cache postorder b3,b5,b4,b2,b1
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 3 "early deadcode"
f b1 t1 a1 29 5
b b1 Plain p32:66:31:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
b b2 If p32:67:10:0:0 0 0 - v17 b4:0,b3:0 b1:0
v v15 Trunc64to32 t3 0 - p32:66:31:0:0 3 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b4 Plain p32:68:33:1:0 0 0 - - b5:0 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b4:0
v v25 Trunc64to32 t3 0 - p32:68:33:0:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v15,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b5,b4,b2,b1
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 4 "short circuit"
f b2 t1 a1 29 5
b b1 BlockInvalid p32:66:31:1:0 0 0 - - - -
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 3 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b4 BlockInvalid p32:68:33:1:0 0 0 - - - -
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v15,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb -
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 5 "decompose user"
f b2 t1 a1 29 5
b b1 BlockInvalid p32:66:31:1:0 0 0 - - - -
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 3 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b4 BlockInvalid p32:68:33:1:0 0 0 - - - -
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v15,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb -
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 6 "pre-opt deadcode"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 3 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v15,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 7 "opt"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 3 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v15,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 8 "zero arg cse"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 3 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v15,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 9 "opt deadcode"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 3 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v15,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 10 "generic cse"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 3 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v15,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 11 "phiopt"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 3 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v15,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 12 "gcse deadcode"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 3 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v15,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 13 "nilcheckelim"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v16 Const32 t3 64 - p0:0:0:0:0 1 -
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 3 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v15,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 14 "prove"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 15 "divisible"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 16 "divmod"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 17 "middle opt"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 18 "known bits"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 19 "early fuse"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p32:65:6:2:0 1 -
v v8 Arg t2 0 a4 p32:65:6:2:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v24,v23,v19,v18,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 20 "expand calls"
aux a10 nameoff "u1+0" a3 0
aux a11 nameoff "u2+0" a4 0
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
v v24 SB t15 0 - p0:0:0:0:0 0 -
v v23 SP t15 0 - p0:0:0:0:0 2 -
v v19 OffPtr t33 0 - p0:0:0:0:0 0 v23
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
v v18 LocalAddr t18 0 a5 p32:70:2:1:0 0 v23,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 0=v19,64=v12,v16
freev v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 21 "decompose builtin"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
v v24 SB t15 0 - p0:0:0:0:0 0 -
v v23 SP t15 0 - p0:0:0:0:0 2 -
v v19 OffPtr t33 0 - p0:0:0:0:0 0 v23
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
v v18 LocalAddr t18 0 a5 p32:70:2:1:0 0 v23,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 0=v19,64=v12,v16
freev v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 22 "softfloat"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
v v24 SB t15 0 - p0:0:0:0:0 0 -
v v23 SP t15 0 - p0:0:0:0:0 2 -
v v19 OffPtr t33 0 - p0:0:0:0:0 0 v23
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
v v18 LocalAddr t18 0 a5 p32:70:2:1:0 0 v23,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 0=v19,64=v12,v16
freev v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 23 "branchelim"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
v v24 SB t15 0 - p0:0:0:0:0 0 -
v v23 SP t15 0 - p0:0:0:0:0 2 -
v v19 OffPtr t33 0 - p0:0:0:0:0 0 v23
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
v v18 LocalAddr t18 0 a5 p32:70:2:1:0 0 v23,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 0=v19,64=v12,v16
freev v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 24 "late opt"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v18,v19,v23,v24,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 25 "dead auto elim"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v18,v19,v23,v24,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 26 "sccp"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v18,v19,v23,v24,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 27 "generic deadcode"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v18,v19,v23,v24,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 28 "late fuse"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v18,v19,v23,v24,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 29 "check bce"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v18,v19,v23,v24,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 30 "dse"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v18,v19,v23,v24,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 31 "memcombine"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v18,v19,v23,v24,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 32 "writebarrier"
f b2 t1 a1 29 5
b b2 If p32:67:10:0:0 0 0 - v17 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v12 Const64 t11 64 - p0:0:0:0:0 2 -
v v16 Const32 t3 64 - p0:0:0:0:0 2 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v11 BitLen64 t11 0 - p289:37:54:1:0 1 v7
v v13 Sub64 t11 0 - p289:37:47:0:0 1 v12,v11
v v15 Trunc64to32 t3 0 - p32:66:31:1:0 2 v13
v v17 Eq32 t4 0 - p32:67:7:1:0 1 v15,v16
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v15,v26
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v21 BitLen64 t11 0 - p290:37:54:1:0 1 v8
v v22 Sub64 t11 0 - p290:37:47:0:0 1 v12,v21
v v25 Trunc64to32 t3 0 - p32:68:33:1:0 1 v22
v v26 Add32 t3 0 - p32:68:5:0:0 1 v16,v25
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts 64=v12,v16
freev v18,v19,v23,v24,v28,v14,v9,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 33 "lower"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 34 "addressing modes"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 35 "late lower"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 36 "pair"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s4,s5,s6
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v8
named s6 v22
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 37 "lowered deadcode for cse"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 38 "lowered cse"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 39 "elim unread autos"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 40 "tighten tuple selectors"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 41 "lowered deadcode"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 42 "checkLower"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 43 "loop invariant"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 44 "late phielim and copyelim"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 45 "tighten"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache loopnest 6 0 - -
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 46 "late deadcode"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b4,b1
cache postorder b3,b5,b2
cache idom b2:-,b3:b2,b5:b2
cache sdom b2:-:b5:-:2:17,b3:b2:-:-:11:14,b5:b2:-:b3:5:8
cache loopnest 6 0 - -
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 47 "critical"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b4:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b4:0,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
b b4 Plain p32:67:10:0:0 0 0 - - b3:0 b2:1
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b1
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 48 "phi tighten"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b4:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b4:0,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
b b4 Plain p32:67:10:0:0 0 0 - - b3:0 b2:1
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b1
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 49 "likelyadjust"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b4:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b3 Ret p32:70:2:1:0 0 0 - v29 - b4:0,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
b b4 Plain p32:67:10:0:0 0 0 - - b3:0 b2:1
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b1
cache postorder b3,b5,b4,b2
cache idom b2:-,b3:b2,b5:b2,b4:b2
cache sdom b2:-:b4:-:2:23,b3:b2:-:-:17:20,b5:b2:-:b3:11:14,b4:b2:-:b5:5:8
cache loopnest 6 0 - -
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
dcllen 8
end
pass 50 "layout"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b4:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
b b4 Plain p32:67:10:0:0 0 0 - - b3:0 b2:1
b b3 Ret p32:70:2:1:0 0 0 - v29 - b4:0,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b1
cache postorder b3,b5,b4,b2
cache idom b2:-,b5:b2,b4:b2,b3:b2
cache sdom b2:-:b4:-:2:23,b5:b2:-:b3:11:14,b4:b2:-:b5:5:8,b3:b2:-:-:17:20
cache loopnest 6 0 - -
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
fstate laidout
dcllen 8
end
pass 51 "schedule"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b4:0 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
b b4 Plain p32:67:10:0:0 0 0 - - b3:0 b2:1
b b3 Ret p32:70:2:1:0 0 0 - v29 - b4:0,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b1
cache postorder b3,b5,b4,b2
cache idom b2:-,b5:b2,b4:b2,b3:b2
cache sdom b2:-:b4:-:2:23,b5:b2:-:b3:11:14,b4:b2:-:b5:5:8,b3:b2:-:-:17:20
cache loopnest 6 0 - -
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
fstate scheduled,laidout
dcllen 8
end
pass 52 "late nilcheck"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b4:0 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
b b4 Plain p32:67:10:0:0 0 0 - - b3:0 b2:1
b b3 Ret p32:70:2:1:0 0 0 - v29 - b4:0,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b1
cache postorder b3,b5,b4,b2
cache idom b2:-,b5:b2,b4:b2,b3:b2
cache sdom b2:-:b4:-:2:23,b5:b2:-:b3:11:14,b4:b2:-:b5:5:8,b3:b2:-:-:17:20
cache loopnest 6 0 - -
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
fstate scheduled,laidout
dcllen 8
end
pass 53 "flagalloc"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b4:0 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
b b4 Plain p32:67:10:0:0 0 0 - - b3:0 b2:1
b b3 Ret p32:70:2:1:0 0 0 - v29 - b4:0,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v24,v26,v25,v22,v21,v14,v18,v17,v15,v13,v11,v16,v12,v6,v5,v4,v3,v2
freeb b1
cache postorder b3,b5,b4,b2
cache idom b2:-,b5:b2,b4:b2,b3:b2
cache sdom b2:-:b4:-:2:23,b5:b2:-:b3:11:14,b4:b2:-:b5:5:8,b3:b2:-:-:17:20
cache loopnest 6 0 - -
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
fstate scheduled,laidout
dcllen 8
end
pass 54 "regalloc"
aux a1 call "AuxCall{math.lz}" a2 1 2 1 8 16 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t2 a4 1 8
abiparam out 0 t3 a5 0 -1
callreg 0:1 - 0 -
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b4:0 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
b b4 Plain p32:67:10:0:0 0 0 - - b3:0 b2:1
b b3 Ret p32:70:2:1:0 0 0 - v29 - b4:0,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v2,v3,v4,v5,v6,v11,v12,v13,v14,v15,v16,v17,v18,v21,v22,v24,v25,v26
freeb b1
cache postorder b3,b5,b4,b2
cache idom b2:-,b5:b2,b4:b2,b3:b2
cache sdom b2:-:b4:-:2:23,b5:b2:-:b3:11:14,b4:b2:-:b5:5:8,b3:b2:-:-:17:20
cache loopnest 6 0 - -
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
fstate scheduled,laidout
regalloc 30 v7:R0,v8:R1,v9:R0,v19:R0,v27:R0,v28:R1,v29:[]
dcllen 8
end
pass 55 "loop rotate"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b4:0 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
b b4 Plain p32:67:10:0:0 0 0 - - b3:0 b2:1
b b3 Ret p32:70:2:1:0 0 0 - v29 - b4:0,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v2,v3,v4,v5,v6,v11,v12,v13,v14,v15,v16,v17,v18,v21,v22,v24,v25,v26
freeb b1
cache postorder b3,b5,b4,b2
cache idom b2:-,b5:b2,b4:b2,b3:b2
cache sdom b2:-:b4:-:2:23,b5:b2:-:b3:11:14,b4:b2:-:b5:5:8,b3:b2:-:-:17:20
cache loopnest 6 0 - -
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
fstate scheduled,laidout
regalloc 30 v7:R0,v8:R1,v9:R0,v19:R0,v27:R0,v28:R1,v29:[]
dcllen 8
end
pass 56 "trim"
f b2 t1 a1 29 5
b b2 ARM64EQ p32:67:10:0:0 0 0 - v23 b5:0,b3:0 -
v v7 ArgIntReg t2 0 a10 p32:67:10:0:0 1 -
v v8 ArgIntReg t2 1 a11 p32:67:10:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v19 ARM64CLZ t11 0 - p289:37:54:1:0 2 v7
v v10 InlMark t30 233 - p32:66:31:1:0 0 v1
v v23 ARM64CMPWconst t29 64 - p32:67:7:1:0 1 v19
b b5 Plain p32:68:33:0:0 0 0 - - b3:1 b2:0
v v28 ARM64CLZ t11 0 - p290:37:54:1:0 1 v8
v v20 InlMark t30 234 - p32:68:33:1:0 0 v1
v v9 ARM64ADDconst t11 64 - p290:37:47:0:0 1 v28
b b3 Ret p32:70:2:1:0 0 0 - v29 - b2:1,b5:0
v v27 Phi t3 0 - p32:70:2:0:0 1 v19,v9
v v29 MakeResult t34 0 - p32:70:2:1:0 1 v27,v1
names s1,s2,s3,s5
named s1 v7
named s2 v8
named s3 v7
named s5 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t11/0/-/0=s4,a8/t2/0/-/0=s5,a9/t11/0/-/0=s6
consts -
freev v2,v3,v4,v5,v6,v11,v12,v13,v14,v15,v16,v17,v18,v21,v22,v24,v25,v26
freeb b1
cache auxmap a3:1,a4:2,-:3,a10:4,a11:5
cache linestarts 32:66:70,289:37:37,290:37:37
fstate scheduled,laidout
regalloc 30 v7:R0,v8:R1,v9:R0,v19:R0,v27:R0,v28:R1,v29:[]
dcllen 8
end
frontend
end
ptrcache t2,t3,t6,t7,t8,t10,t11,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t5,t8,t6,t9,t3,t10,t7,t2,t11,t14,t15,t25,t26,t12,t13,t4,t17,t18,t19,t33,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t34
eof
"#

/-- `std/std/math/lz,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "math"
func "lz" 1
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
type t1 8 8 0 0 - "uint64"
name n1 "u1" PPARAM t1 1 "math.u1" 0 a3
name n2 "u2" PPARAM t1 1 "math.u2" 0 a4
type t2 4 4 0 0 - "int32"
name n3 "l" PPARAMOUT t2 1 "math.l" 0 a5
name n4 "x" PAUTO t1 1 "math/bits.x" 0 a6
type t3 8 8 0 0 - "int"
name n5 "~r0" PAUTO t3 1 "math.~r0" 0 a7
name n6 "x" PAUTO t1 1 "math/bits.x" 0 a8
name n7 "~r0" PAUTO t3 1 "math.~r0" 0 a9
name n8 ".autotmp_7" PAUTO t3 3 "math..autotmp_7" 0 -
in n1 0 used
in n2 8 used
in n3 0 used,outregs
in n4 0 used
in n5 0 -
in n6 0 used
in n7 0 -
in n8 0 used,autotmp
out n1 0 used
out n2 8 used
opt n8 0 autotmp
opt n4 0 -
opt n6 0 -
opt n5 0 -
opt n7 0 -
opt n3 0 outregs
stack 0 0 8
end
genin
posbase p32 "math/fma.go" 1 1 -1 31 "math/fma.go" "math/fma.go" 1 1
sym y1 "math.lz" 1
curfn p32:65:6:0:0 0 0
regargs 8192:0:t1,8193:8:t1
text y1 0 0 0 0 65 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "math.lz.arginfo1" 0
sym y4 "math.lz.argliveinfo" 0
sym y5 "math/bits.LeadingZeros64" 1
inl i233 - p32:66:31:0:0 y5 "LeadingZeros64"
posbase p289 "math/bits/bits.go" 1 1 233 53 "math/bits/bits.go" "math/bits/bits.go" 1 1
inl i234 - p32:68:33:0:0 y5 "LeadingZeros64"
posbase p290 "math/bits/bits.go" 1 1 234 53 "math/bits/bits.go" "math/bits/bits.go" 1 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 0 p32:65:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p32:65:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p32:65:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p32:65:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p32:65:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p32:65:6:2:0
p 14 14 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p32:65:6:1:0
p 6 6 0 0 0 - CLZ 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p289:37:54:1:0
p 7 7 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p32:66:31:1:0
p 8 8 0 0 0 - CMPW 0 CONST/0/0/0/NONE/0/64/-/- 8192 - _ 0 0 p32:67:7:1:0
p 9 9 0 0 0 - BNE 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@13 0 0 p32:67:10:2:0
p 10 10 0 0 0 - CLZ 0 REG/8193/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p290:37:54:1:0
p 11 11 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p32:68:33:1:0
p 12 12 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/64/-/- 8193 - REG/8192/0/0/NONE/0/0/-/- 0 0 p290:37:47:2:0
p 13 13 0 0 0 - RET 0 _ 0 - _ 0 0 p32:70:2:1:0
p 15 15 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 65 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
inlmark @7 233
inlmark @11 234
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 2
dbgslot 0 n1 t1 0
dbgslot 1 n2 t1 0
dbgslot 2 n4 t1 0
dbgslot 3 n6 t1 0
dbgvar 0 n1 0
dbgvar 1 n2 1
dbgvar 2 n4 2
dbgvar 3 n6 3
dbgloc 0 2:-10000:2:19:50
dbgloc 1 2:-10000:5:28:51
dbgloc 2 2:-10000:2:19:50
dbgloc 3 2:-10000:5:28:51
dbgregout n3
dbgpc 2:19:7,5:28:11
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 2 p32:65:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p32:65:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p32:65:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p32:65:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p32:65:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p32:65:6:2:0
p 14 0 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p32:65:6:1:0
p 6 4 0 0 91 - CLZ 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p289:37:54:1:0
p 7 8 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p32:66:31:1:0
p 8 12 0 0 96 - CMPW 0 CONST/0/0/0/NONE/17/64/-/- 8192 - NONE/0/0/0/NONE/1/0/-/- 0 0 p32:67:7:1:0
p 9 16 0 0 80 - BNE 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/13/-/@13 0 0 p32:67:10:2:0
p 10 20 0 0 91 - CLZ 0 REG/8193/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p290:37:54:1:0
p 11 24 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p32:68:33:1:0
p 12 28 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/64/-/- 8193 - REG/8192/0/0/NONE/2/0/-/- 0 0 p290:37:47:2:0
p 13 32 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p32:70:2:1:0
fn y1 16 0 0 0 65 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
inlmark @7 233
inlmark @11 234
funcaux y2 y2 - - y3 y4 -
text 48 0 1f2003d50010c0da1f2003d51f000171810000542110c0da1f2003d520000191c0035fd6000000000000000000000000 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y2,_,_,_,y3,y4
usedfiles 31,53
inltree 0 -1 p32:66:31:0:0 y5 "LeadingZeros64" 8
inltree 1 -1 p32:68:33:0:0 y5 "LeadingZeros64" 24
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 5 1 8000 00080808ff 0
data y4 SDATA 2 1 8000 0000 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 040c00 0
data y10 SRODATA 3 1 28000 020c00 0
data y11 SRODATA 15 1 28000 40012c012b032c012b012c012b0400 0
data y12 SRODATA 18 1 28000 84010137013a0102023b013e013d01420400 0
data y13 SRODATA 15 1 28000 000102010103040103010401030400 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.math.lz$abstract" 0
sym y18 "" 0
posbase p55 "math/bits/bits.go" 1 1 -1 53 "math/bits/bits.go" "math/bits/bits.go" 1 1
sym y19 "go:info.math/bits.LeadingZeros64$abstract" 0
sym y20 "go:info.uint64" 0
sym y21 "go:info.int32" 0
sym y22 "type:int32" 0
dwfn y14 y15 y16 y17 y18 "math.lz" 31:65 1 0 1 177
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2,n3
dwprecursor y1 y17 n1,n2,n3
dwinlfn y5 y19
dwinldcl y5 "x" 0 p55:37:21:0:0
dwinldcl y5 "~r0" 0 p55:37:31:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "uint64" 0 0 1 p32:65:9:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "uint64" 0 0 1 p32:65:13:0:0
dwname n8 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p289:37:54:0:0
dwname n4 1 0 0 1 0 0 0 0 - - "uint64" 0 0 1 p289:37:21:0:0
dwname n6 1 0 0 1 0 0 0 0 - - "uint64" 0 0 1 p290:37:21:0:0
dwname n5 1 0 0 1 0 0 0 0 - - "int" 0 0 1 p289:37:31:0:0
dwname n7 1 0 0 1 0 0 0 0 - - "int" 0 0 1 p290:37:31:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "int32" 0 0 1 p32:65:25:0:0
var 0 0 "u1" 5 1 0 0 0 8 y20 "math/fma.go" 65 9 0 0 1 0 v0
var 1 0 "u2" 5 1 0 0 0 16 y20 "math/fma.go" 65 13 0 1 1 0 v1
var 2 0 "l" 5 1 1 0 0 0 y21 "math/fma.go" 65 25 0 2 1 0 -
var 3 0 "x" 5 1 0 1 0 -8 y20 "math/bits/bits.go" 37 21 234 0 1 0 v2
var 4 0 "x" 5 1 0 1 0 -8 y20 "math/bits/bits.go" 37 21 235 0 1 0 v3
scope 0 0 - 0,1,2,3,4
inlcall 0 233 31:66 y19 - 1 4:8 3
inlcall 1 234 31:68 y19 - 1 20:24,28:32 4
dieref y14 3 y17 0
dieref y14 5 y17 1
dieref y14 7 y17 2
dieref y14 10 y19 0
dieref y14 14 y19 0
dieoff y17 0:12,1:21,2:30
data y14 SDWARFFCN 83 0 0 0600000000000030019c2900000000000000002900000000000000002a000000000009000000000000000020000000422900000000000000000009000000000000000020000000442900000000000000000000 16
reloc 0 0 R_USETYPE 0 y22
reloc 1 4 R_DWARFSECREF 0 y17
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y17
reloc 15 4 R_DWARFSECREF 0 y15
reloc 20 4 R_DWARFSECREF 0 y17
reloc 24 4 R_DWARFSECREF 9 y15
reloc 29 4 R_DWARFSECREF 0 y17
reloc 35 4 R_DWARFSECREF 0 y19
reloc 39 4 R_DWARFSECREF 0 y16
reloc 49 4 R_DWARFSECREF 0 y19
reloc 53 4 R_DWARFSECREF 18 y15
reloc 59 4 R_DWARFSECREF 0 y19
reloc 63 4 R_DWARFSECREF 7 y16
reloc 73 4 R_DWARFSECREF 0 y19
reloc 77 4 R_DWARFSECREF 27 y15
data y15 SDWARFLOC 36 0 0 010000040008015000010000040018015100010000040008015000010000040018015100 4
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
reloc 19 2 R_DWTXTADDR_U2 0 y1
reloc 28 2 R_DWTXTADDR_U2 0 y1
data y16 SDWARFRANGE 17 0 0 01000004040800010000041418041c2000 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 8 2 R_DWTXTADDR_U2 0 y1
data y18 SDWARFLINES 57 0 0 00090200000000000000000420033b140436036833042003183c3806370436060366330420031a3c043606036533042006031c3c0210000101 1
reloc 3 8 R_ADDR 0 y1
data y17 SDWARFABSFCN 39 0 1 056d6174682e6c7a00014101227531000000000000227532000000000000226c00010000000000 3
reloc 17 4 R_DWARFSECREF 0 y20
reloc 26 4 R_DWARFSECREF 0 y20
reloc 34 4 R_DWARFSECREF 0 y21
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `math.lz`. -/
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

/-- The PC table `checkG58` computes (`b2`, `b5`, `b3`: one entry per value, then the
terminator). -/
def tab : PcTab := [(2, [5, 5, 5, 5, 8, 8, 10]), (5, [11, 12, 12, 14]), (3, [14, 14, 14])]

/-- The class table `checkG58` computes. -/
def kt : KTab :=
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)

def blk5 : Block := (lc.ctx.f.block? 5).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: GenG2's, a 16-byte frame with 8 bytes of extra space. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, no home slot, the PC table `tab`. -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The 64-bit word in `R0` at `b5`'s jump (`v9`, of class 64). -/
def w0 : BitVec 64 := 0xffffffff00000045

/-- The `runLoc` state at `b5`'s jump: `w0` in `R0`, every other register `poison`, the empty
memory. -/
def sT : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w64 w0 else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine at `b5`'s jump: `X0 = w0`, the activation's `g` and `FP`, a zero memory. -/
def mT : MState :=
  { x := fun k => if k = 0 then w0 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 5 3, mem := fun _ => 0 }

/-- The register holds the 64-bit `w0`. -/
def isW64 : Option Val → Bool
  | some (.int .w64 x) => x == w0
  | _ => false

theorem isW64_spec {o : Option Val} (h : isW64 o = true) : o = some (.int .w64 w0) := by
  unfold isW64 at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- The read gives the 32-bit `0x45`. -/
def isRd32 : Res Val → Bool
  | .ok (.int .w32 x) => x == 0x45
  | _ => false

theorem isRd32_spec {o : Res Val} (h : isRd32 o = true) : o = .ok (.int .w32 0x45) := by
  unfold isRd32 at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- What compiled evaluation checks on `math.lz`: it is lowered; `checkG58` accepts it with `tab`
and `kt`; its Progs have IDs below `2^32`; no frame variable is accessed and there is no home
slot; `b5` is a block of it with three values, ending in a plain jump; the class table holds `R0`
at 64 bits at `b5`'s end and at 32 bits at `b3`'s start; `v29` reads `R0` at 32 bits; `v27` is
homed in `R0` at class 32; G35's table at `b5`'s end is empty; and `stepTermLoc` runs `b5`'s jump
from `sT` to `b3`, keeping `w0` in `R0`, where `v27` reads `0x45`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered && (checkG58 lc0 ps bs g).toOption == some (tab, kt) &&
    ps.toList.all (·.id < 2 ^ 32) && (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 5 && (lc.ctx.f.block? 5).isSome && blk5.values.size == 3 &&
    blk5.kind == .Plain && (kAt lc kt 5 blk5 3).get 0 == some 64 &&
    (kt.at 3).get 0 == some 32 && kReads lc (val 29) == [(0, 32)] &&
    lc.home 27 == some (.reg 0) && cls (lc.ty 27) == some 32 && uL35 lc (uIn35 lc 5) blk5 3 == [] &&
    GenG1.okThen (stepTermLoc lc sT blk5) fun r =>
      GenG1.gotoIs r.1 3 && isW64 r.2.regs[0]? && isRd32 (r.2.read lc 27)

theorem g59k_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG58 lc0 ps bs g = .ok (tab, kt) ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 5 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 5 = some blk5 ∧ blk5.values.size = 3 ∧ blk5.kind = .Plain ∧
      (kAt lc kt 5 blk5 3).get 0 = some 64 ∧ (kt.at 3).get 0 = some 32 ∧
      kReads lc (val 29) = [(0, 32)] ∧ lc.home 27 = some (.reg 0) ∧ cls (lc.ty 27) = some 32 ∧
      uL35 lc (uIn35 lc 5) blk5 3 = [] ∧
      GenG1.okThen (stepTermLoc lc sT blk5)
        (fun r => GenG1.gotoIs r.1 3 && isW64 r.2.regs[0]? && isRd32 (r.2.read lc 27)) = true := by
  have hf := g59k_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    List.all_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hl, hres, hlt, hav, hsl, hm5, hb5s, hsz, hkind, hk5, hk3, hrd, hh, hc, hu, hrun⟩ := hf
  refine ⟨hl, ?_, hlt, hav, hsl, hm5, ?_, hsz, hkind, hk5, hk3, hrd, hh, hc, hu, hrun⟩
  · revert hres; cases checkG58 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb5s
    simp [blk5, hb]

/-! ## The activation -/

theorem env59k (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hav : (accessedVars lc).isEmpty = true)
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

/-! ## `b5`'s jump -/

theorem sT_regs {r : Nat} {x : Val} (h : sT.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w64 w0) ∨ x = .poison := by
  simp only [sT, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    by_cases h0 : r = 0
    · subst h0; simp
    · simp [h0]
  · cases h

theorem locMatchT : LocMatch E sT 5 3 mT where
  regs := by
    intro r v hv
    rcases sT_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl (by decide)
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [sT] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, mT, E]; decide,
    by simp only [MState.word, readMem, mT, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

/-- The invariant at `b5`'s end: `R0` at its class, 64 bits. -/
theorem invT (hk0 : (kAt lc kt 5 blk5 3).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 5 blk5 3) sT where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, by simp [KeysNodup, GenG2.mem0],
      fun b al a h => by simp [GenG2.mem0] at h⟩
    rcases sT_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [hk0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [sT] at h

/-- **G59, group K, on `math.lz`** (`func lz(u1, u2 uint64) (l int32)`: two 64-bit counts joined
into its 32-bit result): `checkG58` accepts it, with `v29` reading `R0` at 32 bits where the class
table holds `R0` at 64 bits at the end of `b5` and at 32 bits at `b3`'s start. From `sT`, with the
64-bit `0xffffffff00000045` in `R0`, `g58_term` runs `b5`'s jump to a machine state related before
`b3`'s first value at the class table there, whose `X0` keeps the 64-bit word; `v27` (`Phi`, 32
bits, `R0`) reads its low word `0x45`, related to `X0` by `arg_rel`. -/
theorem genG59k_witness :
    checkG58 lc0 ps bs g = .ok (tab, kt) ∧ kReads lc (val 29) = [(0, 32)] ∧
      (kAt lc kt 5 blk5 3).get 0 = some 64 ∧ (kt.at 3).get 0 = some 32 ∧
      ∃ s1 e m1, stepTermLoc lc sT blk5 = .ok (.goto e, s1) ∧ e.b = 3 ∧
        s1.regs[0]? = some (.int .w64 0xffffffff00000045) ∧
        PStar GenG2.H0 L ps.toList 0 mT m1 ∧ LocMatch E s1 3 0 m1 ∧ G3Inv E lc (kt.at 3) s1 ∧
        s1.read lc 27 = .ok (.int .w32 0x45) ∧ m1.x 0 = 0xffffffff00000045 ∧
        (m1.x 0).setWidth 32 = 0x45 := by
  obtain ⟨hl, hc, hlt, hav, hsl, hm5, hb5, hsz, hkind, hk5, hk3, hrd, hh, hcl, hu, hrun⟩ := facts
  have hE := env59k hlt hav hsl
  obtain ⟨⟨n, s1⟩, hs1, hrun⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨⟨hgo, hr0⟩, hr27⟩ := hrun
  have hr0 := isW64_spec hr0
  have hr27 := isRd32_spec hr27
  obtain ⟨e, rfl, het⟩ := GenG1.gotoIs_spec hgo
  -- `g58_term` reads the blocks of `lc0`: rewrite rather than unfold (the kernel would evaluate
  -- `lc0`).
  have hm0 : 5 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm5
  have hb0 : lc0.ctx.f.block? 5 = some blk5 := by rw [← liveCtx_ctx (lc := lc0)]; exact hb5
  obtain ⟨m1, hp1, hlm1, hinv1, -, -⟩ := g58_term (H := GenG2.H0) hc hE hm0 hb0
    (by rw [hsz]; exact locMatchT) (by rw [hsz]; exact invT hk5)
    (fun hz => by rw [hkind] at hz; rcases hz with h | h <;> cases h)
    (by
      change UOKL mT (uL35 lc (uIn35 lc 5) blk5 blk5.values.size)
      rw [hsz, hu]
      intro e he
      cases he)
    hs1
  rw [het] at hlm1 hinv1
  have hx0 : m1.x 0 = w0 :=
    valRel_i64 GenG2.addrAgree ((hlm1.regs 0 _ hr0).1 0 (objX?_low (by decide)))
  obtain ⟨x, hx, hxr, -⟩ := arg_rel GenG2.addrAgree hl hlm1 hinv1.core hh hcl (fun _ => hk3)
    (Or.inr ⟨by decide, objX?_low (by decide)⟩)
  rw [hr27] at hx
  cases hx
  have hlo : (m1.x 0).setWidth 32 = 0x45 := by
    have h := hxr
    rw [rX_lt (by decide)] at h
    exact h
  exact ⟨hc, hrd, hk5, hk3, s1, e, m1, hs1, het, hr0, hp1, hlm1, hinv1, hr27, hx0, hlo⟩

end GoFV.Proof.Witness.GenG59k
