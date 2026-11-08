import GoFV.Proof.Gen.G18
import GoFV.Proof.Witness.GenG17

/-!
# Non-vacuity witness: slice G18 of the genssa validator on `main.setpf` (`test/ken_array`)

`test/ken_array/main/setpf,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`): `setpf`
(`test/ken_array.go`), `for i := 0; i < 20; i++ { a[i] = i }` with `a *[20]int`.

`checkG17` rejects it (`v19 = MOVDstoreidx8`); `checkG18` accepts it with the PC table `tab` and
the class table `kt`. Block `b4` (the loop body): `v13 = LoweredNilCheck v5 v25`,
`v19 = MOVDstoreidx8 v5 v7 v7 v25` (`a` in `R0`, `i` in `R1`), `v22 = ADDconst [1] v7`. Its
Progs: `MOVB (R0), ZR`, `MOVD R1, (R0)(R1<<3)`, `ADD $1, R1, R1`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g18_facts`),
`stepLoc` runs `v19` from a state with `a` the start of the heap object `heap 1` of 8 bytes 7
(`mem7`) in `R0` and the index `i = 0` in `R1`: the memory is then `memZ`, the 8 bytes 0. On a
framed activation with `G10Env` (as `GenG13`'s, `heap 1` injected at `2^41`) and the machine
memory holding the object's bytes there (`M7`), `g18_value` runs `MOVD R1, (R0)(R1<<3)` and gives
the state before `v22`, the memory `memZ` related to the machine's: the 8 machine bytes at `A`
are then 0 (`genG18_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG18

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/ken_array/main/setpf,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "setpf" 1 0 0
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
type t4 INT 8 8 0 comparable,named "int" "int"
type t3 ARRAY 160 8 0 comparable "[20]int" "[20]int" t4 20
type t2 PTR 8 8 8 hasptr,direct,comparable "*[20]int" "*[20]int" t3
type t1 FUNC 8 8 8 hasptr,direct "func(*[20]int)" "func(*[20]int)" 0 1 0
field 0 "a" t2 ? 0
aux a2 sym "main.setpf" "main.setpf" 1 - 0 - - - - 0
posbase p2 "./array.go" 1 1 -1
aux a3 name "a" "a" PPARAM t2 0 1 used p2:28:12:0:0
aux a1 call "AuxCall{main.setpf}" a2 1 1 0 8 8 1 0
abiparam in 0 t2 a3 0 0
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
type t15 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t16 UINT 8 8 0 comparable,named "uint" "uint"
type t17 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t18 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t8
type t21 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t12
type t22 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t4
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
type t35 PTR 8 8 8 hasptr,direct,comparable "**[20]int" "**[20]int" t2
aux a4 type "int" t4
slot s1 a3 t2 0 - 0
aux a5 name "i" "i" PAUTO t4 0 1 used p2:30:6:0:0
slot s2 a5 t4 0 - 0
f b1 t1 a1 26 7
typs Bool=t5,Int8=t6,Int16=t7,Int32=t8,Int64=t9,UInt8=t10,UInt16=t11,UInt32=t12,UInt64=t13,Int=t4,Float32=t14,Float64=t15,UInt=t16,Uintptr=t17,String=t18,BytePtr=t19,Int32Ptr=t20,UInt32Ptr=t21,IntPtr=t22,UintptrPtr=t23,Float32Ptr=t24,Float64Ptr=t25,BytePtrPtr=t26,Complex64=t27,Complex128=t28,UnsafePtr=t29,Mem=t30,Flags=t31,Void=t32,Int128=t33,ResultMem=t34
b b1 Plain p2:30:2:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 2 v6,v22
v v9 Less64 t5 0 - p2:30:16:0:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 2 v1,v19
v v26 Phi t2 0 - p2:30:16:0:0 1 v5,v11
b b3 If p2:31:4:0:0 1 0 - v14 b6:0,b7:0 b2:0
v v10 Copy t4 0 - p2:31:8:2:0 5 v7
v v11 Copy t2 0 - p2:31:4:2:0 2 v26
v v12 Copy t30 0 - p2:31:4:2:0 3 v25
v v13 NilCheck t2 0 - p2:31:4:0:0 1 v11,v12
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v10,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b6:0
v v20 Copy t4 0 - p2:30:27:2:0 1 v10
v v22 Add64 t4 0 - p2:30:27:0:0 1 v20,v21
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v23 Copy t30 0 - p2:33:1:2:0 1 v25
v v24 MakeResult t34 0 - p2:33:1:0:0 1 v23
b b6 Plain p2:31:4:0:0 0 0 - - b4:0 b3:0
v v17 PtrIndex t22 0 - p2:31:4:0:0 1 v13,v10
v v18 Copy t30 0 - p2:31:8:2:0 1 v12
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v10,v18
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v15 Copy t30 0 - p2:31:4:2:0 1 v12
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v10,v8,v15
names s1,s2
named s1 v5,v11,v26
named s2 v6,v7,v10,v20,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 2 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 2 v1,v19
v v26 Phi t2 0 - p2:30:16:0:0 1 v5,v11
b b3 If p2:31:4:0:0 1 0 - v14 b6:0,b7:0 b2:0
v v10 Copy t4 0 - p2:31:8:2:0 5 v7
v v11 Copy t2 0 - p2:31:4:2:0 2 v26
v v12 Copy t30 0 - p2:31:4:2:0 3 v25
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v11,v12
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v10,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b6:0
v v20 Copy t4 0 - p2:30:27:2:0 1 v10
v v22 Add64 t4 0 - p2:30:27:1:0 1 v20,v21
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v23 Copy t30 0 - p2:33:1:2:0 1 v25
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v23
b b6 Plain p2:31:4:0:0 0 0 - - b4:0 b3:0
v v17 PtrIndex t22 0 - p2:31:4:0:0 1 v13,v10
v v18 Copy t30 0 - p2:31:8:2:0 1 v12
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v10,v18
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v15 Copy t30 0 - p2:31:4:2:0 1 v12
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v10,v8,v15
names s1,s2
named s1 v5,v11,v26
named s2 v6,v7,v10,v20,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev -
freeb -
cache postorder b4,b6,b7,b3,b5,b2,b1
cache linestarts 2:30:33
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p2:28:6:2:0 3 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 8 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 8 v1,v19
v v26 Copy t2 0 - p2:30:16:0:0 0 v5
b b3 If p2:31:4:0:0 1 0 - v14 b6:0,b7:0 b2:0
v v10 Copy t4 0 - p2:31:8:2:0 0 v7
v v11 Copy t2 0 - p2:31:4:2:0 0 v5
v v12 Copy t30 0 - p2:31:4:2:0 0 v25
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b6:0
v v20 Copy t4 0 - p2:30:27:2:0 0 v7
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v23 Copy t30 0 - p2:33:1:2:0 0 v25
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b6 Plain p2:31:4:0:0 0 0 - - b4:0 b3:0
v v17 PtrIndex t22 0 - p2:31:4:0:0 1 v13,v7
v v18 Copy t30 0 - p2:31:8:2:0 0 v25
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v15 Copy t30 0 - p2:31:4:2:0 0 v25
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5,v5,v5
named s2 v6,v7,v7,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev -
freeb -
cache postorder b4,b6,b7,b3,b5,b2,b1
cache linestarts 2:30:33
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 6 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
b b3 If p2:31:4:0:0 1 0 - v14 b6:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b6:0
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b6 Plain p2:31:4:0:0 0 0 - - b4:0 b3:0
v v17 PtrIndex t22 0 - p2:31:4:0:0 1 v13,v7
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v15,v18,v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb -
cache postorder b4,b6,b7,b3,b5,b2,b1
cache linestarts 2:30:33
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 6 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
b b3 If p2:31:4:0:0 1 0 - v14 b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v17 PtrIndex t22 0 - p2:31:4:0:0 1 v13,v7
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b6 BlockInvalid p2:31:4:0:0 0 0 - - - -
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v15,v18,v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb -
cache linestarts 2:30:33
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 6 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
b b3 If p2:31:4:0:0 1 0 - v14 b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v17 PtrIndex t22 0 - p2:31:4:0:0 1 v13,v7
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b6 BlockInvalid p2:31:4:0:0 0 0 - - - -
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v15,v18,v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb -
cache linestarts 2:30:33
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 6 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
b b3 If p2:31:4:0:0 1 0 - v14 b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v17 PtrIndex t22 0 - p2:31:4:0:0 1 v13,v7
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v15,v18,v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache linestarts 2:30:33
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 6 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
b b3 If p2:31:4:0:0 1 0 - v14 b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v15 Mul64 t4 0 - p2:31:4:0:0 1 v7,v18
v v18 Const64 t4 8 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache linestarts 2:30:33
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
v v18 Const64 t4 8 - p2:31:4:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 6 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
b b3 If p2:31:4:0:0 1 0 - v14 b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v15 Mul64 t4 0 - p2:31:4:0:0 1 v7,v18
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache linestarts 2:30:33
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
v v18 Const64 t4 8 - p2:31:4:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 6 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
b b3 If p2:31:4:0:0 1 0 - v14 b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v15 Mul64 t4 0 - p2:31:4:0:0 1 v7,v18
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache linestarts 2:30:33
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
v v18 Const64 t4 8 - p2:31:4:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 6 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
b b3 If p2:31:4:0:0 1 0 - v14 b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v15 Mul64 t4 0 - p2:31:4:0:0 1 v7,v18
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
v v18 Const64 t4 8 - p2:31:4:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 6 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
b b3 If p2:31:4:0:0 1 0 - v14 b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v15 Mul64 t4 0 - p2:31:4:0:0 1 v7,v18
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
v v18 Const64 t4 8 - p2:31:4:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 6 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
b b3 If p2:31:4:0:0 1 0 - v14 b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v15 Mul64 t4 0 - p2:31:4:0:0 1 v7,v18
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
v v18 Const64 t4 8 - p2:31:4:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 6 v6,v22
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
b b3 If p2:31:4:0:0 1 0 - v14 b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 1 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v15 Mul64 t4 0 - p2:31:4:0:0 1 v7,v18
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 3 -
v v18 Const64 t4 8 - p2:31:4:0:0 1 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 6 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v14 IsInBounds t5 0 - p2:31:4:0:0 0 v7,v8
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Mul64 t4 0 - p2:31:4:0:0 1 v7,v18
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 2 -
v v18 Const64 t4 8 - p2:31:4:0:0 1 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 5 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Mul64 t4 0 - p2:31:4:0:0 1 v7,v18
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v14,v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 2 -
v v18 Const64 t4 8 - p2:31:4:0:0 1 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 5 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Mul64 t4 0 - p2:31:4:0:0 1 v7,v18
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v14,v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 2 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 5 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v18,v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 2 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 5 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v18,v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:28:6:2:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 2 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 5 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v18,v23,v20,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 20 "expand calls"
aux a6 nameoff "a+0" a3 0
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 2 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
v v18 SB t17 0 - p0:0:0:0:0 0 -
v v23 SP t17 0 - p0:0:0:0:0 1 -
v v20 OffPtr t35 0 - p0:0:0:0:0 0 v23
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 5 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,v20,1=v21,20=v8
freev v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 2 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
v v18 SB t17 0 - p0:0:0:0:0 0 -
v v23 SP t17 0 - p0:0:0:0:0 1 -
v v20 OffPtr t35 0 - p0:0:0:0:0 0 v23
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 5 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,v20,1=v21,20=v8
freev v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 2 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
v v18 SB t17 0 - p0:0:0:0:0 0 -
v v23 SP t17 0 - p0:0:0:0:0 1 -
v v20 OffPtr t35 0 - p0:0:0:0:0 0 v23
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 5 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,v20,1=v21,20=v8
freev v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 2 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
v v18 SB t17 0 - p0:0:0:0:0 0 -
v v23 SP t17 0 - p0:0:0:0:0 1 -
v v20 OffPtr t35 0 - p0:0:0:0:0 0 v23
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 5 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,v20,1=v21,20=v8
freev v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 2 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 5 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v20,v23,v18,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 2 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 5 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v20,v23,v18,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 2 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
v v20 ConstBool t5 1 - p2:30:16:1:0 0 -
v v23 Const64 t4 1 - p2:30:27:1:0 0 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 5 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 4 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 First p2:31:4:0:0 1 0 - - b4:0,b7:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
b b7 Exit p2:31:4:0:0 0 0 - v16 - b3:1
v v16 PanicBounds t30 0 - p2:31:4:0:0 1 v7,v8,v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v18,v12,v11,v10,v26,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 1 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b3:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 Plain p2:31:4:0:0 0 0 - - b4:0 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b3:0
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v16,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b7,b6
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 1 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 BlockInvalid p2:31:4:0:0 0 0 - - - -
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v16,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b7,b6
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 1 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 BlockInvalid p2:31:4:0:0 0 0 - - - -
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v16,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b7,b6
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 1 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 BlockInvalid p2:31:4:0:0 0 0 - - - -
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v16,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b7,b6
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 1 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 BlockInvalid p2:31:4:0:0 0 0 - - - -
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v16,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b7,b6
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 Const64 t4 0 - p0:0:0:0:0 1 -
v v8 Const64 t4 20 - p0:0:0:0:0 1 -
v v21 Const64 t4 1 - p0:0:0:0:0 1 -
b b2 If p2:30:21:0:0 1 0 - v9 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v9 Less64 t5 0 - p2:30:16:1:0 1 v7,v8
b b3 BlockInvalid p2:31:4:0:0 0 0 - - - -
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 NilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v15 Lsh64x64 t4 1 - p2:31:4:0:0 1 v7,v14
v v22 Add64 t4 0 - p2:30:27:1:0 1 v7,v21
v v17 AddPtr t22 0 - p2:31:4:0:0 1 v13,v15
v v19 Store t30 0 a4 p2:31:8:0:0 1 v17,v7,v25
v v14 Const64 t13 3 - p2:31:4:0:0 1 -
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts 0=v6,1=v21,20=v8
freev v16,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b7,b6
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64MOVDconst t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b3 BlockInvalid p2:31:4:0:0 0 0 - - - -
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b7,b6
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64MOVDconst t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b3 BlockInvalid p2:31:4:0:0 0 0 - - - -
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b7,b6
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b3 BlockInvalid p2:31:4:0:0 0 0 - - - -
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b7,b6
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b3 BlockInvalid p2:31:4:0:0 0 0 - - - -
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b7,b6
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache auxmap a3:1,-:2
cache linestarts 2:30:33
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b4:0
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b4:0
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b4:0
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b4:0
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b4:0
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t2 0 - p2:31:4:1:0 1 v5,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v13,v7,v7,v25
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b4:0
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t32 0 - p2:31:4:1:0 0 v5,v25
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v5,v7,v7,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b4:0
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t32 0 - p2:31:4:1:0 0 v5,v25
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v5,v7,v7,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b4:0
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v6,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t32 0 - p2:31:4:1:0 0 v5,v25
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v5,v7,v7,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v14,v17,v15,v9,v21,v8,v23,v20,v18,v12,v11,v10,v26,v4,v3,v2
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b4:0
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
v v14 Copy t4 0 - p2:30:2:2:0 1 v6
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v14,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t32 0 - p2:31:4:1:0 0 v5,v25
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v5,v7,v7,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v2,v3,v4,v8,v9,v10,v11,v12,v15,v17,v18,v20,v21,v23,v26
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b4:b2:-:-:14:17,b5:b2:-:b4:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b4:0
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
fstate scheduled,laidout
regalloc 23 v5:R0,v6:ZERO,v7:R1,v14:R1,v22:R1
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
v v14 Copy t4 0 - p2:30:2:2:0 1 v6
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t32 0 - p2:31:4:1:0 0 v5,v25
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v5,v7,v7,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v14,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v2,v3,v4,v8,v9,v10,v11,v12,v15,v17,v18,v20,v21,v23,v26
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b4:b2,b2:b1,b5:b2
cache sdom b1:-:b2:-:2:23,b4:b2:-:-:14:17,b2:b1:b5:-:5:20,b5:b2:-:b4:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b4:0
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
hotness b4:3
fstate scheduled,laidout
regalloc 23 v5:R0,v6:ZERO,v7:R1,v14:R1,v22:R1
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 26 7
b b1 Plain p2:30:2:1:0 0 0 - - b2:0 -
v v5 ArgIntReg t2 0 a6 p2:30:2:1:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v6 ARM64ZERO t4 0 - p0:0:0:0:0 1 -
v v14 Copy t4 0 - p2:30:2:2:0 1 v6
b b4 Plain p2:30:27:0:0 0 0 - - b2:1 b2:0
v v13 ARM64LoweredNilCheck t32 0 - p2:31:4:1:0 0 v5,v25
v v19 ARM64MOVDstoreidx8 t30 0 - p2:31:8:0:0 1 v5,v7,v7,v25
v v22 ARM64ADDconst t4 1 - p2:30:27:1:0 1 v7
b b2 ARM64LT p2:30:21:0:0 1 0 - v16 b4:0,b5:0 b1:0,b4:0
v v7 Phi t4 0 - p2:30:16:0:0 4 v14,v22
v v25 Phi t30 0 - p2:30:16:0:0 3 v1,v19
v v16 ARM64CMPconst t31 20 - p2:30:16:1:0 1 v7
b b5 Ret p2:33:1:0:0 0 0 - v24 - b2:1
v v24 MakeResult t34 0 - p2:33:1:1:0 1 v25
names s1,s2
named s1 v5
named s2 v6,v7,v22
splits -
canon a3/t2/0/-/0=s1,a5/t4/0/-/0=s2
consts -
freev v2,v3,v4,v8,v9,v10,v11,v12,v15,v17,v18,v20,v21,v23,v26
freeb b3,b7,b6
cache postorder b4,b5,b2,b1
cache idom b1:-,b4:b2,b2:b1,b5:b2
cache sdom b1:-:b2:-:2:23,b4:b2:-:-:14:17,b2:b1:b5:-:5:20,b5:b2:-:b4:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b4:0
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:30:33
hotness b4:3
fstate scheduled,laidout
regalloc 23 v5:R0,v6:ZERO,v7:R1,v14:R1,v22:R1
dcllen 2
end
frontend
end
ptrcache t3,t4,t7,t8,t9,t10,t12,t14,t15,t17,t18,t19,t26
typelink t30=t34
typeorder t6,t10,t7,t11,t8,t12,t9,t13,t4,t16,t17,t27,t28,t14,t15,t5,t19,t20,t21,t22,t23,t24,t25,t26,t35,t2,t1,t3,t18,t29,t30,t32,t31,t33,t34
eof
"#

/-- `test/ken_array/main/setpf,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "setpf" 1
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
type t1 8 8 8 1 01 "*[20]int"
name n1 "a" PPARAM t1 1 "main.a" 0 a3
type t2 8 8 0 0 - "int"
name n2 "i" PAUTO t2 1 "main.i" 0 a5
in n1 0 used
in n2 0 used
out n1 0 used
opt n2 0 -
stack 0 0 8
end
genin
posbase p2 "./array.go" 1 1 -1 1 "./array.go" "./array.go" 1 1
sym y1 "main.setpf" 1
curfn p2:28:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 28 201080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "main.setpf.arginfo1" 0
sym y5 "main.setpf.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:28:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:28:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:28:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:28:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:28:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:28:6:2:0
p 6 6 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:30:2:1:0
p 7 7 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@11 0 0 p2:30:2:2:0
p 8 8 0 0 0 - MOVB 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8219/0/0/NONE/0/0/-/- 0 0 p2:31:4:1:0
p 9 9 0 0 0 - MOVD 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/8192/8801/0/NONE/0/0/-/- 0 0 p2:31:8:2:0
p 10 10 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/1/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:30:27:1:0
p 11 11 0 0 0 - CMP 0 CONST/0/0/0/NONE/0/20/-/- 8193 - _ 0 0 p2:30:16:1:0
p 12 12 0 0 0 - BLT 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@8 0 0 p2:30:21:2:0
p 13 13 0 0 0 - RET 0 _ 0 - _ 0 0 p2:33:1:0:0
p 14 14 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 28 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
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
dbgloc 0 1:-10000:-1:-30000:50
dbgloc 1 1:14:-1:-30000:50
dbgregout -
dbgpc 1:14:7
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p2:28:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:28:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:28:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:28:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p2:28:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:28:6:2:0
p 6 0 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:30:2:1:0
p 7 4 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/11/-/@11 0 0 p2:30:2:2:0
p 15 8 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p2:30:2:2:0
p 8 8 0 0 294 - MOVB 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8219/0/0/NONE/2/0/-/- 0 0 p2:31:4:1:0
p 16 12 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:31:4:1:0
p 9 12 0 0 314 - MOVD 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/8192/8801/0/NONE/114/0/-/- 0 0 p2:31:8:2:0
p 10 16 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/1/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:30:27:1:0
p 11 20 0 0 96 - CMP 0 CONST/0/0/0/NONE/18/20/-/- 8193 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:30:16:1:0
p 12 24 0 0 80 - BLT 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/8/-/@8 0 0 p2:30:21:2:0
p 13 28 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:33:1:0:0
fn y1 8 0 0 0 28 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 32 0 e1031faa040000141b008039017821f8210400913f5000f18bffff54c0035fd6 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y3,_,_,_,y4,y5
usedfiles 1
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y6 SRODATA 7 1 28000 00020101020500 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 040800 0
data y10 SRODATA 3 1 28000 020800 0
data y11 SRODATA 3 1 28000 040800 0
data y12 SRODATA 9 1 28000 3e0202020103060100 0
data y13 SRODATA 3 1 28000 000800 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.main.setpf$abstract" 0
sym y18 "" 0
sym y19 "go:info.*[20]int" 0
sym y20 "go:info.int" 0
dwfn y14 y15 y16 y17 y18 "main.setpf" 1:28 1 0 1 12
dwdcl n1
dwclosure 0 -
dwmark p2:30:2:0:0 1
dwmark p2:32:2:0:0 0
dwparents 0
dwparams n1
dwprecursor y1 y17 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "*[20]int" 0 0 1 p2:28:12:0:0
dwname n2 1 0 0 0 0 0 0 0 - - "int" 0 0 1 p2:30:6:0:0
var 0 0 "a" 5 1 0 0 0 8 y19 "./array.go" 28 12 0 0 1 0 v0
var 1 0 "i" 52 1 0 0 0 -8 y20 "./array.go" 30 6 0 1 1 0 v1
scope 0 0 0:32 0
scope 1 0 0:28 1
dieref y14 2 y17 0
dieref y14 5 y17 1
dieoff y17 0:15,1:23
data y14 SDWARFFCN 34 0 0 06000000000020019c2900000000000000000c000000002300000000000000000000 7
reloc 1 4 R_DWARFSECREF 0 y17
reloc 5 1 R_DWTXTADDR_U1 0 y1
reloc 10 4 R_DWARFSECREF 0 y17
reloc 14 4 R_DWARFSECREF 0 y15
reloc 19 4 R_DWARFSECREF 0 y16
reloc 24 4 R_DWARFSECREF 0 y17
reloc 28 4 R_DWARFSECREF 8 y15
data y15 SDWARFLOC 16 0 0 01000400200150000100040420015000 2
reloc 1 1 R_DWTXTADDR_U1 0 y1
reloc 9 1 R_DWTXTADDR_U1 0 y1
data y16 SDWARFRANGE 6 0 0 010004001c00 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y18 SDWARFLINES 33 0 0 000902000000000000000004020318140637063806370636065f063a0204000101 1
reloc 3 8 R_ADDR 0 y1
data y17 SDWARFABSFCN 32 0 1 056d61696e2e736574706600011c0122610000000000002169001e0000000000 2
reloc 19 4 R_DWARFSECREF 0 y19
reloc 27 4 R_DWARFSECREF 0 y20
end
eof
"#

/-- The loaded `setpf` (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG18` gives (`b1`: `MOVD ZR, R1` after the no-op Progs from 5, then `JMP`;
`b4`: `v13`'s `MOVB`, `v19`'s `MOVD`, `v22`'s `ADD`; `b2`: `CMP` and `BLT`; `b5`: `RET`). -/
def tab : PcTab := [(1, [5, 5, 5, 5, 7]), (4, [8, 9, 10, 11]), (2, [11, 11, 11, 12]), (5, [13, 13])]

/-- The class table `checkG18` gives (`R0` and `R1` of class 64 in the loop). -/
def kt : KTab := (match checkG18 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

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
at `symA`, `heap 1` at `2^41` and the PC table of `checkG18`. -/
def E : MatchEnv :=
  { lc, ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The argument `a`: the start of the heap object `heap 1`. -/
def pB : Ptr := ⟨.heap 1, 0⟩

/-- The Phase 1 memory before `v19`: `heap 1` a block of 8 bytes 7. -/
def mem7 : Mem := { blocks := #[(.heap 1, { data := Array.replicate 8 (.b 7) })], nextHeap := 2 }

/-- The Phase 1 memory after `v19`: `heap 1` holds the word 0. -/
def memZ : Mem := { blocks := #[(.heap 1, { data := Array.replicate 8 (.b 0) })], nextHeap := 2 }

/-- The machine memory before `v19`: the 8 bytes 7 of `heap 1` at `A`, 0 elsewhere. -/
def M7 : Memory := fun y => if (y - A).toNat < 8 then 7 else 0

/-- The `runLoc` state before `v19`: `a` (`pB`) in `R0`, the index 0 in `R1`, every other
register `poison`, the memory `mem7`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem7 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 0 then .ptr pB else if i.val = 1 then .i64 0 else .poison,
    flags := .poison, slots := [], mem := .mem mem7 }

/-- The machine before `v19`: `X0` the address `A` of `a`, `X1` 0, the activation's `g` and
`FP`, the PC of `v19`, the memory `M7`. -/
def m0 : MState :=
  { x := fun k => if k = 0 then A else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 4 1, mem := M7 }

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

/-- What compiled evaluation checks on `setpf`: `checkG18` accepts it with `tab` and `kt` and
`checkG17` does not; it accesses no frame variable and has no home slot; `b4` holds `v19` at
index 1, a `MOVDstoreidx8`, and `R0` and `R1` have class 64 before it; `stepLoc` runs `v19` from
`s0` to the memory `memZ`; and no 8 bytes of `memZ`'s block encode a pointer. -/
def gFacts : Bool :=
  (checkG18 lc ps bs g).toOption == some (tab, kt) && (checkG17 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 4 && (lc.ctx.f.block? 4).isSome &&
    (lc.ctx.f.value? 19).isSome && blk4.values[1]? == some 19 &&
    (val 19).op == .ARM64MOVDstoreidx8 &&
    (kAt lc kt 4 blk4 1).get 0 == some 64 && (kAt lc kt 4 blk4 1).get 1 == some 64 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 19)) memIsZ &&
    (List.range 8).all fun o => ptrWordAt? (Array.replicate 8 (.b 0)) o == none

theorem g18_facts : gFacts = true := by
  native_decide

/-- The facts of `g18_facts` as hypotheses. -/
theorem facts :
    checkG18 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 4 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 4 = some blk4 ∧ lc.ctx.f.value? 19 = some (val 19) ∧
      blk4.values[1]? = some 19 ∧ (val 19).op = .ARM64MOVDstoreidx8 ∧
      (kAt lc kt 4 blk4 1).get 0 = some 64 ∧ (kAt lc kt 4 blk4 1).get 1 = some 64 ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 19)) memIsZ = true ∧
      ∀ o, o < 8 → ptrWordAt? (Array.replicate 8 (.b 0)) o = none := by
  have hf := g18_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hm4⟩, hb4s⟩, hv19⟩, hi1⟩, hop⟩, hk0⟩, hk1⟩, hrun⟩,
    hpw⟩ := hf
  refine ⟨?_, hav, hsl, hm4, ?_, ?_, hi1, hop, hk0, hk1, hrun, hpw⟩
  · revert hres; cases checkG18 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb4s
    simp [blk4, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv19
    simp [val, hv]

theorem g18Env (hc : checkG18 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG18_spec hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := GenG12.addrAgree
        glob := fun _ _ _ _ => rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG18_spec hc
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
    b = .heap 1 ∧ al = { data := Array.replicate 8 (.b 7) } := by
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

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .ptr pB) ∨ (r = 1 ∧ x = .i64 0) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · split at h
      · rename_i _ h1; exact Or.inr (Or.inl ⟨h1, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatch0 : LocMatch E s0 4 1 m0 where
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
  mem := ⟨mem7, rfl, memInj7⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, M7, E, A]; decide,
    by simp only [MState.word, readMem, m0, M7, E, A]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g18Inv0 (h0 : (kAt lc kt 4 blk4 1).get 0 = some 64)
    (h1 : (kAt lc kt 4 blk4 1).get 1 = some 64) :
    G3Inv E lc (kAt lc kt 4 blk4 1) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem7, rfl, keys7, sep7⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · rw [h1] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

theorem g7Pre_of {v : Value} (h1 : v.op ≠ .ARM64CMP) (h2 : v.op ≠ .ARM64CMPconst)
    (h3 : loadOp? v.op = none) (h4 : v.op ≠ .ARM64LDP) (h5 : v.op ≠ .ARM64SUB)
    (h6 : v.op ≠ .ARM64LoweredNilCheck) (s : LocState) : G7Pre lc s v :=
  ⟨⟨⟨fun h => by rcases h with h | h <;> contradiction,
    (fun _ _ _ hl => by rw [h3] at hl; cases hl), fun h => absurd h h5⟩, fun h => absurd h h4⟩,
    fun h => absurd h h6⟩

/-- **G18 on `setpf`**: from the state before `v19` with `a` (`pB`) in `R0`, the index 0 in `R1`
and `heap 1` 8 bytes 7 (`mem7`, at `A` in `M7`), `g18_value` runs the register-index store `v19`
(`MOVD R1, (R0)(R1<<3)`) and gives the state before `v22`, with the memory `memZ` related to the
machine's under an activation that extends `E` and is a `G10Env`: the 8 machine bytes at `A` are
then 0. -/
theorem genG18_value_witness :
    ∃ s1 E' m1, stepLoc GenG2.env lc s0 (val 19) = .ok s1 ∧ s1.mem = .mem memZ ∧
      E.Extends E' ∧ G10Env lc g L ps 0 tab E' ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E' s1 4 2 m1 ∧ G3Inv E' lc (kAt lc kt 4 blk4 2) s1 ∧
      ∀ i, i < 8 → m1.mem (A + BitVec.ofNat 64 i) = 0 := by
  obtain ⟨hc, hav, hsl, hm4, hb, hv19, hi1, hop, hk0, hk1, hrun, hpw⟩ := facts
  obtain ⟨s1, hs1, hz⟩ := GenG1.okThen_spec hrun
  have hE := g18Env hc hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64MOVDstoreidx8 → (val 19).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', hinv1⟩ := g18_value (H := GenG2.H0) (env := GenG2.env) hc
    hE hm4 hb hi1 hv19 (by rw [hop]; rfl) locMatch0 (g18Inv0 hk0 hk1)
    ⟨⟨g7Pre_of (hne _ (by decide)) (hne _ (by decide)) (by rw [hop]; simp [loadOp?, narrowLoad?])
      (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide)) _,
      fun h => absurd h (hne _ (by decide))⟩,
      fun _ _ _ _ hl => by rw [hop] at hl; simp [loadIdxOp?] at hl⟩
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  refine ⟨s1, E1, m1, hs1, memIsZ_spec hz, hx1, hE1, hp1, hm1', hinv1, fun i hi => ?_⟩
  obtain ⟨mm, hmm, hMI⟩ := hm1'.mem
  rw [memIsZ_spec hz] at hmm
  cases hmm
  obtain ⟨W, hW⟩ := hMI.bytes
  have hA : E1.ι (.heap 1) = some A := hx1.2 _ _ rfl
  obtain ⟨hw, -, hby⟩ := hW (.heap 1) { data := Array.replicate 8 (.b 0) } A (by simp [memZ]) hA
  have hnw : ∀ o, ¬ W (.heap 1) o := by
    intro o ho
    obtain ⟨p, hp, -⟩ := hw o ho
    by_cases ho8 : o < 8
    · rw [hpw o ho8] at hp; cases hp
    · simp [ptrWordAt?] at hp; omega
  have := hby i (by simpa using hi) (fun o ho => absurd ho (hnw o))
  simp only [Array.getElem_replicate, ByteRel] at this
  exact this.symm

end GoFV.Proof.Witness.GenG18
