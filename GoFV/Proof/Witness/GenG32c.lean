import GoFV.Proof.Witness.GenG32

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G32's `CSINC` on `internal/bytealg.countGeneric`

`std/std/internal/bytealg/countGeneric,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`):

```go
func countGeneric(b []byte, c byte) int {
	n := 0
	for _, x := range b {
		if x == c {
			n++
		}
	}
	return n
}
```

`checkG30` rejects it (`CSINC` is G32's op); `checkG32` accepts it with the PC table `tab` and the
class table `kt`. The loop body `b3`: `v20 = MOVBUloadidx v37 v11 v1` (`MOVBU (R0)(R3), R5`),
`v34 = MOVDnop v20`, `v40 = CMPW v39 v34` (`CMPW R5, R2`), `v32 = CSINC [NotEqual] v31 v31 v40`
(`CSINC NE, R4, R4, R4`: `n` if `x ≠ c`, else `n + 1`), `v27 = ADDconst [1] v11`
(`ADD $1, R3, R3`).

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g32c_facts`),
`stepLoc` runs `v32` from a state with `n = 5` in `R4` and the flags of `CMPW R5, R2` on `x = c`
(`EQ`, so `NotEqual` fails): `R4` then holds `5 + 1` (the `y + 1` branch). On a framed activation
with `G28Env` (`GenG32.envOf`) with `X4 = 5` and `NZCV` those flags, `g32_value` runs the `CSINC`:
the machine's `X4` is `5 + 1` (`genG32_csinc_witness`).
-/

namespace GoFV.Proof.Witness.GenG32c

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen
open GoFV.Proof.Witness.GenG32 (Lof Eof envOf mem0 memInj0)

/-- `std/std/internal/bytealg/countGeneric,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "internal/bytealg"
func "countGeneric" 1 0 0
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
config localpkg "internal/bytealg"
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
type t3 UINT8 1 1 0 comparable,named "byte" "uint8"
type t2 SLICE 24 8 8 hasptr "[]byte" "[]uint8" t3
type t4 INT 8 8 0 comparable,named "int" "int"
type t1 FUNC 8 8 8 hasptr,direct "func([]byte, byte) int" "func([]uint8, uint8) int" 0 2 1
field 0 "b" t2 ? 0
field 1 "c" t3 ? 0
field 2 "" t4 ? 0
aux a2 sym "internal/bytealg.countGeneric" "internal/bytealg.countGeneric" 1 - 0 - - - - 0
posbase p4 "internal/bytealg/count_native.go" 1 1 -1
aux a3 name "b" "b" PPARAM t2 0 1 used p4:16:19:0:0
aux a4 name "c" "c" PPARAM t3 24 1 used p4:16:29:0:0
aux a5 name "~r0" "~r0" PPARAMOUT t4 0 1 - p4:16:37:0:0
aux a1 call "AuxCall{internal/bytealg.countGeneric}" a2 1 2 1 8 32 4 1
abiparam in 0 t2 a3 0,1,2 0
abiparam in 1 t3 a4 3 24
abiparam out 0 t4 a5 0 -1
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
type t35 PTR 8 8 8 hasptr,direct,comparable "*[]byte" "*[]uint8" t2
type t36 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t3
type t37 RESULTS ? ? ? - "int,mem" "" 2 t4,t30
slot s1 a3 t2 0 - 0
slot s2 a4 t3 0 - 0
aux a6 name "n" "n" PAUTO t4 0 1 used p4:17:2:0:0
slot s3 a6 t4 0 - 0
aux a7 name "x" "x" PAUTO t3 0 1 used p4:18:9:0:0
slot s4 a7 t3 0 - 0
f b1 t1 a1 40 7
typs Bool=t5,Int8=t6,Int16=t7,Int32=t8,Int64=t9,UInt8=t10,UInt16=t11,UInt32=t12,UInt64=t13,Int=t4,Float32=t14,Float64=t15,UInt=t16,Uintptr=t17,String=t18,BytePtr=t19,Int32Ptr=t20,UInt32Ptr=t21,IntPtr=t22,UintptrPtr=t23,Float32Ptr=t24,Float64Ptr=t25,BytePtrPtr=t26,Complex64=t27,Complex128=t28,UnsafePtr=t29,Mem=t30,Flags=t31,Void=t32,Int128=t33,ResultMem=t34
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 3 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t22 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:0:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 2 v9,v27
v v12 Phi t4 0 - p4:18:14:0:0 2 v10,v40
v v13 Less64 t5 0 - p4:18:14:0:0 1 v11,v12
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v33 Phi t30 0 - p4:18:14:0:0 2 v1,v34
v v36 Phi t3 0 - p4:18:14:0:0 1 v8,v37
v v38 Phi t2 0 - p4:18:14:0:0 1 v7,v39
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b6:0 b2:0
v v14 Copy t4 0 - p4:18:14:2:0 2 v11
v v15 Copy t2 0 - p4:18:14:2:0 3 v38
v v16 SliceLen t4 0 - p4:18:14:0:0 0 v15
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v15
v v18 PtrIndex t36 0 - p4:18:14:0:0 1 v17,v14
v v19 Copy t30 0 - p4:18:14:2:0 2 v33
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v19
v v21 Copy t3 0 - p4:19:8:2:0 2 v36
v v22 Eq8 t5 0 - p4:19:8:0:0 1 v20,v21
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b6:0
v v26 Copy t4 0 - p4:18:14:2:0 1 v35
v v27 Add64 t4 0 - p4:18:14:0:0 1 v26,v24
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v28 Copy t4 0 - p4:23:2:2:0 1 v31
v v29 Copy t30 0 - p4:23:2:2:0 1 v33
v v30 MakeResult t37 0 - p4:23:2:0:0 1 v28,v29
b b6 Plain p4:18:14:2:0 0 0 - - b4:0 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v34 Copy t30 0 - p4:23:2:2:0 1 v19
v v35 Copy t4 0 - p4:18:14:2:0 1 v14
v v37 Copy t3 0 - p4:19:8:2:0 1 v21
v v39 Copy t2 0 - p4:18:14:2:0 1 v15
v v40 Copy t4 0 - p4:18:14:2:0 1 v12
b b7 Plain p4:20:5:0:0 0 0 - - b6:1 b3:0
v v23 Copy t4 0 - p4:20:5:2:0 1 v31
v v25 Add64 t4 0 - p4:20:5:0:0 1 v23,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8,v21,v36,v37
named s3 v9,v23,v25,v28,v31,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev -
freeb -
dcllen 8
end
pass 1 "number lines"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 3 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t22 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 2 v9,v27
v v12 Phi t4 0 - p4:18:14:0:0 2 v10,v40
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v12
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v33 Phi t30 0 - p4:18:14:0:0 2 v1,v34
v v36 Phi t3 0 - p4:18:14:0:0 1 v8,v37
v v38 Phi t2 0 - p4:18:14:0:0 1 v7,v39
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b6:0 b2:0
v v14 Copy t4 0 - p4:18:14:2:0 2 v11
v v15 Copy t2 0 - p4:18:14:2:0 3 v38
v v16 SliceLen t4 0 - p4:18:14:0:0 0 v15
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v15
v v18 PtrIndex t36 0 - p4:18:14:0:0 1 v17,v14
v v19 Copy t30 0 - p4:18:14:2:0 2 v33
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v19
v v21 Copy t3 0 - p4:19:8:2:0 2 v36
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v21
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b6:0
v v26 Copy t4 0 - p4:18:14:2:0 1 v35
v v27 Add64 t4 0 - p4:18:14:1:0 1 v26,v24
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v28 Copy t4 0 - p4:23:2:2:0 1 v31
v v29 Copy t30 0 - p4:23:2:2:0 1 v33
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v28,v29
b b6 Plain p0:0:0:0:0 0 0 - - b4:0 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v34 Copy t30 0 - p4:23:2:2:0 1 v19
v v35 Copy t4 0 - p4:18:14:2:0 1 v14
v v37 Copy t3 0 - p4:19:8:2:0 1 v21
v v39 Copy t2 0 - p4:18:14:2:0 1 v15
v v40 Copy t4 0 - p4:18:14:2:0 1 v12
b b7 Plain p4:20:5:0:0 0 0 - - b6:1 b3:0
v v23 Copy t4 0 - p4:20:5:2:0 1 v31
v v25 Add64 t4 0 - p4:20:5:1:0 1 v23,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8,v21,v36,v37
named s3 v9,v23,v25,v28,v31,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev -
freeb -
cache postorder b4,b6,b7,b3,b5,b2,b1
cache linestarts 4:18:23
dcllen 8
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v2 SP t17 0 - p0:0:0:0:0 3 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t22 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p4:16:6:2:0 6 -
v v8 Arg t3 0 a4 p4:16:6:2:0 4 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 3 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 6 v9,v27
v v12 Copy t4 0 - p4:18:14:0:0 0 v10
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
v v31 Phi t4 0 - p4:18:14:0:0 5 v9,v32
v v33 Copy t30 0 - p4:18:14:0:0 0 v1
v v36 Copy t3 0 - p4:18:14:0:0 0 v8
v v38 Copy t2 0 - p4:18:14:0:0 0 v7
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b6:0 b2:0
v v14 Copy t4 0 - p4:18:14:2:0 0 v11
v v15 Copy t2 0 - p4:18:14:2:0 0 v7
v v16 SliceLen t4 0 - p4:18:14:0:0 0 v7
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 PtrIndex t36 0 - p4:18:14:0:0 1 v17,v11
v v19 Copy t30 0 - p4:18:14:2:0 0 v1
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v21 Copy t3 0 - p4:19:8:2:0 0 v8
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b6:0
v v26 Copy t4 0 - p4:18:14:2:0 0 v11
v v27 Add64 t4 0 - p4:18:14:1:0 1 v11,v24
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v28 Copy t4 0 - p4:23:2:2:0 0 v31
v v29 Copy t30 0 - p4:23:2:2:0 0 v1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b6 Plain p0:0:0:0:0 0 0 - - b4:0 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v34 Copy t30 0 - p4:23:2:2:0 0 v1
v v35 Copy t4 0 - p4:18:14:2:0 0 v11
v v37 Copy t3 0 - p4:19:8:2:0 0 v8
v v39 Copy t2 0 - p4:18:14:2:0 0 v7
v v40 Copy t4 0 - p4:18:14:2:0 0 v10
b b7 Plain p4:20:5:0:0 0 0 - - b6:1 b3:0
v v23 Copy t4 0 - p4:20:5:2:0 0 v31
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8,v8,v8,v8
named s3 v9,v31,v25,v31,v31,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev -
freeb -
cache postorder b4,b6,b7,b3,b5,b2,b1
cache linestarts 4:18:23
dcllen 8
end
pass 3 "early deadcode"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b6:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 PtrIndex t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b6:0
v v27 Add64 t4 0 - p4:18:14:1:0 1 v11,v24
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b6 Plain p0:0:0:0:0 0 0 - - b4:0 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
b b7 Plain p4:20:5:0:0 0 0 - - b6:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v23,v40,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb -
cache postorder b4,b6,b7,b3,b5,b2,b1
cache linestarts 4:18:23
dcllen 8
end
pass 4 "short circuit"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 PtrIndex t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v11,v24
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b6 BlockInvalid p0:0:0:0:0 0 0 - - - -
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v23,v40,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb -
cache linestarts 4:18:23
dcllen 8
end
pass 5 "decompose user"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 PtrIndex t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v11,v24
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b6 BlockInvalid p0:0:0:0:0 0 0 - - - -
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v23,v40,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb -
cache linestarts 4:18:23
dcllen 8
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 PtrIndex t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v11,v24
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v23,v40,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache linestarts 4:18:23
dcllen 8
end
pass 7 "opt"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v11,v24
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache linestarts 4:18:23
dcllen 8
end
pass 8 "zero arg cse"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v11,v24
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache linestarts 4:18:23
dcllen 8
end
pass 9 "opt deadcode"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v11,v24
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache linestarts 4:18:23
dcllen 8
end
pass 10 "generic cse"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 11 "phiopt"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 12 "gcse deadcode"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 13 "nilcheckelim"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 14 "prove"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 15 "divisible"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 16 "divmod"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 17 "middle opt"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 18 "known bits"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 19 "early fuse"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p4:16:6:2:0 2 -
v v8 Arg t3 0 a4 p4:16:6:2:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v40,v23,v39,v37,v35,v34,v29,v28,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 20 "expand calls"
aux a8 nameoff "c+0" a4 0
aux a9 nameoff "b+0" a3 0
aux a10 nameoff "b+8" a3 8
aux a11 nameoff "b+16" a3 16
f b1 t1 a1 40 7
b b1 Plain p4:18:14:0:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 SliceMake t2 0 - p4:18:14:2:0 2 v37,v35,v34
v v8 ArgIntReg t3 3 a8 p4:18:14:0:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v10 SliceLen t4 0 - p4:18:14:1:0 1 v7
v v40 SB t17 0 - p0:0:0:0:0 0 -
v v23 SP t17 0 - p0:0:0:0:0 3 -
v v39 OffPtr t35 0 - p0:0:0:0:0 0 v23
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v34 ArgIntReg t4 2 a11 p4:18:14:2:0 1 -
v v29 OffPtr t36 0 - p0:0:0:0:0 0 v23
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v10
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v17 SlicePtr t36 0 - p4:18:14:0:0 1 v7
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v17,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
v v28 LocalAddr t22 0 a5 p4:23:2:1:0 0 v23,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9,v31,v25,v32
named s4 v20
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,v39,v29,1=v24
freev v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 21 "decompose builtin"
slot s5 a3 t36 0 - 0
slot s6 a3 t4 8 - 0
slot s7 a3 t4 16 - 0
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 SliceMake t2 0 - p4:18:14:2:0 0 v37,v35,v34
v v8 ArgIntReg t3 3 a8 p4:18:14:0:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v40 SB t17 0 - p0:0:0:0:0 0 -
v v23 SP t17 0 - p0:0:0:0:0 3 -
v v39 OffPtr t35 0 - p0:0:0:0:0 0 v23
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 2 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 2 -
v v34 ArgIntReg t4 2 a11 p4:18:14:2:0 1 -
v v29 OffPtr t36 0 - p0:0:0:0:0 0 v23
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v35
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v37,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
v v28 LocalAddr t22 0 a5 p4:23:2:1:0 0 v23,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s4,s2,s3,s5,s6,s7
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
named s7 v34
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,v39,v29,1=v24
freev v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 22 "softfloat"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 SliceMake t2 0 - p4:18:14:2:0 0 v37,v35,v34
v v8 ArgIntReg t3 3 a8 p4:18:14:0:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v40 SB t17 0 - p0:0:0:0:0 0 -
v v23 SP t17 0 - p0:0:0:0:0 3 -
v v39 OffPtr t35 0 - p0:0:0:0:0 0 v23
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 2 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 2 -
v v34 ArgIntReg t4 2 a11 p4:18:14:2:0 1 -
v v29 OffPtr t36 0 - p0:0:0:0:0 0 v23
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b4:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v35
b b3 If p4:19:8:0:0 0 0 - v22 b7:0,b4:0 b2:0
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v37,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
b b4 Plain p4:18:14:0:0 0 0 - - b2:1 b3:1,b7:0
v v32 Phi t4 0 - p0:0:0:0:0 1 v31,v25
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
v v28 LocalAddr t22 0 a5 p4:23:2:1:0 0 v23,v1
b b7 Plain p4:20:5:0:0 0 0 - - b4:1 b3:0
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
names s4,s2,s3,s5,s6,s7
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
named s7 v34
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,v39,v29,1=v24
freev v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 23 "branchelim"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 SliceMake t2 0 - p4:18:14:2:0 0 v37,v35,v34
v v8 ArgIntReg t3 3 a8 p4:18:14:0:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v40 SB t17 0 - p0:0:0:0:0 0 -
v v23 SP t17 0 - p0:0:0:0:0 3 -
v v39 OffPtr t35 0 - p0:0:0:0:0 0 v23
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 2 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 2 -
v v34 ArgIntReg t4 2 a11 p4:18:14:2:0 1 -
v v29 OffPtr t36 0 - p0:0:0:0:0 0 v23
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v35
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v37,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
v v32 CondSelect t4 0 - p0:0:0:0:0 1 v25,v31,v22
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b4 BlockInvalid p4:18:14:0:0 0 0 - - - -
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
v v28 LocalAddr t22 0 a5 p4:23:2:1:0 0 v23,v1
b b7 BlockInvalid p4:20:5:0:0 0 0 - - - -
names s4,s2,s3,s5,s6,s7
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
named s7 v34
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,v39,v29,1=v24
freev v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 24 "late opt"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:0:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v35
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v37,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
v v32 CondSelect t4 0 - p0:0:0:0:0 1 v25,v31,v22
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b4 BlockInvalid p4:18:14:0:0 0 0 - - - -
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 BlockInvalid p4:20:5:0:0 0 0 - - - -
names s4,s2,s3,s5,s6,s7
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
named s7 v34
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v28,v29,v34,v39,v23,v40,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 25 "dead auto elim"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:0:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v35
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v37,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
v v32 CondSelect t4 0 - p0:0:0:0:0 1 v25,v31,v22
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b4 BlockInvalid p4:18:14:0:0 0 0 - - - -
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 BlockInvalid p4:20:5:0:0 0 0 - - - -
names s4,s2,s3,s5,s6,s7
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
named s7 v34
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v28,v29,v34,v39,v23,v40,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 26 "sccp"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:0:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v28 Const64 t4 1 - p4:20:5:1:0 0 -
v v29 Const64 t4 1 - p4:18:14:1:0 0 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v35
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v37,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
v v32 CondSelect t4 0 - p0:0:0:0:0 1 v25,v31,v22
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b4 BlockInvalid p4:18:14:0:0 0 0 - - - -
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
b b7 BlockInvalid p4:20:5:0:0 0 0 - - - -
names s4,s2,s3,s5,s6,s7
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
named s7 v34
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v34,v39,v23,v40,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 27 "generic deadcode"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v35
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v37,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
v v32 CondSelect t4 0 - p0:0:0:0:0 1 v25,v31,v22
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v29,v28,v34,v39,v23,v40,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23:20=0
dcllen 8
end
pass 28 "late fuse"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v35
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v37,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
v v32 CondSelect t4 0 - p0:0:0:0:0 1 v25,v31,v22
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v29,v28,v34,v39,v23,v40,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23:20=0
dcllen 8
end
pass 29 "check bce"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v35
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v37,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
v v32 CondSelect t4 0 - p0:0:0:0:0 1 v25,v31,v22
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v29,v28,v34,v39,v23,v40,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23:20=0
dcllen 8
end
pass 30 "dse"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v35
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v37,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
v v32 CondSelect t4 0 - p0:0:0:0:0 1 v25,v31,v22
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v29,v28,v34,v39,v23,v40,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23:20=0
dcllen 8
end
pass 31 "memcombine"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v35
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v37,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
v v32 CondSelect t4 0 - p0:0:0:0:0 1 v25,v31,v22
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v29,v28,v34,v39,v23,v40,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23:20=0
dcllen 8
end
pass 32 "writebarrier"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 Const64 t4 0 - p0:0:0:0:0 2 -
v v24 Const64 t4 1 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 If p4:18:14:0:0 1 0 - v13 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v13 Less64 t5 0 - p4:18:14:1:0 1 v11,v35
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v18 AddPtr t36 0 - p4:18:14:0:0 1 v37,v11
v v20 Load t3 0 - p4:18:14:0:0 1 v18,v1
v v22 Eq8 t5 0 - p4:19:8:1:0 1 v20,v8
v v25 Add64 t4 0 - p4:20:5:1:0 1 v31,v24
v v32 CondSelect t4 0 - p0:0:0:0:0 1 v25,v31,v22
v v27 Add64 t4 0 - p4:18:14:1:0 1 v24,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts 0=v9,1=v24
freev v29,v28,v34,v39,v23,v40,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23:20=0
dcllen 8
end
pass 33 "lower"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64MOVDconst t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v20
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23:20=3
dcllen 8
end
pass 34 "addressing modes"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64MOVDconst t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v20
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23:20=3
dcllen 8
end
pass 35 "late lower"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 36 "pair"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v25,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache auxmap a3:1,a4:2,-:3
cache linestarts 4:18:23
dcllen 8
end
pass 38 "lowered cse"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
dcllen 8
end
pass 39 "elim unread autos"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
dcllen 8
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
dcllen 8
end
pass 41 "lowered deadcode"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
dcllen 8
end
pass 42 "checkLower"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
dcllen 8
end
pass 43 "loop invariant"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
dcllen 8
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
dcllen 8
end
pass 45 "tighten"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b3:0
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
dcllen 8
end
pass 46 "late deadcode"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b3:0
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
dcllen 8
end
pass 47 "critical"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b3:0
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
dcllen 8
end
pass 48 "phi tighten"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b3:0
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
dcllen 8
end
pass 49 "likelyadjust"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b3:0
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
dcllen 8
end
pass 50 "layout"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b3:0
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
fstate laidout
dcllen 8
end
pass 51 "schedule"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b3:0
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
fstate scheduled,laidout
dcllen 8
end
pass 52 "late nilcheck"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b3:0
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
fstate scheduled,laidout
dcllen 8
end
pass 53 "flagalloc"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v9,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v9,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v31,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v28,v25,v22,v18,v29,v13,v24,v7,v17,v10,v26,v21,v19,v16,v15,v14,v38,v36,v33,v12,v6,v5,v4,v3,v2
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b3:0
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
fstate scheduled,laidout
dcllen 8
end
pass 54 "regalloc"
aux a1 call "AuxCall{internal/bytealg.countGeneric}" a2 1 2 1 8 32 4 1
abiparam in 0 t2 a3 0,1,2 0
abiparam in 1 t3 a4 3 24
abiparam out 0 t4 a5 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v28 Copy t4 0 - p4:18:14:2:0 1 v9
v v22 Copy t4 0 - p4:18:14:2:0 1 v9
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v28,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v22,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v25 Copy t4 0 - p4:23:2:2:0 1 v31
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v25,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v2,v3,v4,v5,v6,v7,v10,v12,v13,v14,v15,v16,v17,v18,v19,v21,v24,v26,v29,v33,v36,v38
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b5:b2
cache sdom b1:-:b2:-:2:23,b2:b1:b5:-:5:20,b3:b2:-:-:14:17,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b3:0
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
fstate scheduled,laidout
regalloc 40 v8:R3,v9:ZERO,v11:R3,v20:R5,v22:R4,v25:R0,v27:R3,v28:R3,v30:[],v31:R4,v32:R4,v34:R5,v35:R1,v37:R0,v39:R2
dcllen 8
end
pass 55 "loop rotate"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v28 Copy t4 0 - p4:18:14:2:0 1 v9
v v22 Copy t4 0 - p4:18:14:2:0 1 v9
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v28,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v22,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v25 Copy t4 0 - p4:23:2:2:0 1 v31
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v25,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v2,v3,v4,v5,v6,v7,v10,v12,v13,v14,v15,v16,v17,v18,v19,v21,v24,v26,v29,v33,v36,v38
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b3:b2,b2:b1,b5:b2
cache sdom b1:-:b2:-:2:23,b3:b2:-:-:14:17,b2:b1:b5:-:5:20,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b3:0
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
hotness b3:3
fstate scheduled,laidout
regalloc 40 v8:R3,v9:ZERO,v11:R3,v20:R5,v22:R4,v25:R0,v27:R3,v28:R3,v30:[],v31:R4,v32:R4,v34:R5,v35:R1,v37:R0,v39:R2
dcllen 8
end
pass 56 "trim"
f b1 t1 a1 40 7
b b1 Plain p4:18:14:1:0 0 0 - - b2:0 -
v v8 ArgIntReg t3 3 a8 p4:18:14:1:0 1 -
v v37 ArgIntReg t36 0 a9 p4:18:14:2:0 1 -
v v35 ArgIntReg t4 1 a10 p4:18:14:2:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v9 ARM64ZERO t4 0 - p0:0:0:0:0 2 -
v v39 ARM64MOVBUreg t12 0 - p4:19:8:1:0 1 v8
v v28 Copy t4 0 - p4:18:14:2:0 1 v9
v v22 Copy t4 0 - p4:18:14:2:0 1 v9
b b3 Plain p4:19:8:0:0 0 0 - - b2:1 b2:0
v v20 ARM64MOVBUloadidx t3 0 - p4:18:14:0:0 1 v37,v11,v1
v v34 ARM64MOVDnop t12 0 - p4:19:8:1:0 1 v20
v v40 ARM64CMPW t31 0 - p4:19:8:1:0 1 v39,v34
v v32 ARM64CSINC t4 4577 - p0:0:0:0:0 1 v31,v31,v40
v v27 ARM64ADDconst t4 1 - p4:18:14:1:0 1 v11
b b2 ARM64GT p4:18:14:0:0 1 0 - v23 b3:0,b5:0 b1:0,b3:0
v v11 Phi t4 0 - p4:18:14:0:0 3 v28,v27
v v31 Phi t4 0 - p4:18:14:0:0 3 v22,v32
v v23 ARM64CMP t31 0 - p4:18:14:1:0 1 v35,v11
b b5 Ret p4:23:2:1:0 0 0 - v30 - b2:1
v v25 Copy t4 0 - p4:23:2:2:0 1 v31
v v30 MakeResult t37 0 - p4:23:2:1:0 1 v25,v1
names s4,s2,s3,s5,s6
named s4 v20
named s2 v8
named s3 v9,v31,v32
named s5 v37
named s6 v35
splits s1/0/t36=s5,s1/8/t4=s6,s1/16/t4=s7
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2,a6/t4/0/-/0=s3,a7/t3/0/-/0=s4
consts -
freev v2,v3,v4,v5,v6,v7,v10,v12,v13,v14,v15,v16,v17,v18,v19,v21,v24,v26,v29,v33,v36,v38
freeb b7,b4,b6
cache postorder b3,b5,b2,b1
cache idom b1:-,b3:b2,b2:b1,b5:b2
cache sdom b1:-:b2:-:2:23,b3:b2:-:-:14:17,b2:b1:b5:-:5:20,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:2:1:1:0 b2:0,b3:0
cache auxmap a3:1,a4:2,-:3,a8:4,a9:5,a10:6
cache linestarts 4:18:23
hotness b3:3
fstate scheduled,laidout
regalloc 40 v8:R3,v9:ZERO,v11:R3,v20:R5,v22:R4,v25:R0,v27:R3,v28:R3,v30:[],v31:R4,v32:R4,v34:R5,v35:R1,v37:R0,v39:R2
dcllen 8
end
frontend
end
ptrcache t2,t3,t4,t7,t8,t9,t10,t12,t14,t15,t17,t18,t19,t26,t36
typelink t3=t10,t19=t36,t30=t34
typeorder t6,t3=t10,t7,t11,t8,t12,t9,t13,t4,t16,t17,t27,t28,t14,t15,t5,t19=t36,t20,t21,t22,t23,t24,t25,t26,t35,t1,t2,t18,t29,t30,t32,t31,t33,t34,t37
eof
"#

/-- `std/std/internal/bytealg/countGeneric,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "internal/bytealg"
func "countGeneric" 1
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
type t1 24 8 8 1 01 "[]byte"
name n1 "b" PPARAM t1 1 "internal/bytealg.b" 0 a3
type t2 1 1 0 0 - "byte"
name n2 "c" PPARAM t2 1 "internal/bytealg.c" 0 a4
type t3 8 8 0 0 - "int"
name n3 "~r0" PPARAMOUT t3 1 "internal/bytealg.~r0" 0 a5
name n4 "n" PAUTO t3 1 "internal/bytealg.n" 0 a6
name n5 "x" PAUTO t2 1 "internal/bytealg.x" 0 a7
name n6 ".autotmp_5" PAUTO t1 3 "internal/bytealg..autotmp_5" 0 -
name n7 ".autotmp_6" PAUTO t3 3 "internal/bytealg..autotmp_6" 0 -
name n8 ".autotmp_7" PAUTO t3 3 "internal/bytealg..autotmp_7" 0 -
in n1 0 used
in n2 24 used
in n3 0 outregs
in n4 0 used
in n5 0 used
in n6 0 used,autotmp
in n7 0 used,autotmp
in n8 0 used,autotmp
out n1 0 used
out n2 24 used
opt n6 0 autotmp
opt n7 0 autotmp
opt n8 0 autotmp
opt n4 0 -
opt n3 0 outregs
opt n5 0 -
stack 0 0 8
end
genin
posbase p4 "internal/bytealg/count_native.go" 1 1 -1 3 "internal/bytealg/count_native.go" "internal/bytealg/count_native.go" 1 1
type t4 8 8 8 1 01 "*uint8"
sym y1 "internal/bytealg.countGeneric" 1
curfn p4:16:6:0:0 0 0
regargs 8192:0:t4,8193:8:t3,8194:16:t3,8195:24:t2
text y1 0 0 0 0 16 200080
end
prog0
sym y2 "internal/bytealg.b" 0
sym y3 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y4 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y5 "internal/bytealg.countGeneric.arginfo1" 0
sym y6 "internal/bytealg.countGeneric.argliveinfo" 0
type t5 8 8 8 1 01 "*byte"
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i32 0 0 p4:16:6:0:0
p 20 20 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/PARAM/0/0/y2/- 0 0 p4:16:6:2:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p4:16:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p4:16:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p4:16:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p4:16:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p4:16:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p4:19:8:1:0
p 7 7 0 0 0 - MOVBU 0 REG/8195/0/0/NONE/0/0/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p4:19:8:1:0
p 8 8 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p4:18:14:1:0
p 9 9 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8196/0/0/NONE/0/0/-/- 0 0 p4:18:14:2:0
p 10 10 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@15 0 0 p4:18:14:2:0
p 11 11 0 0 0 - MOVBU 0 MEM/8192/8195/0/NONE/0/0/-/- 0 - REG/8197/0/0/NONE/0/0/-/- 0 0 p4:18:14:2:0
p 12 12 0 0 0 - CMPW 0 REG/8197/0/0/NONE/0/0/-/- 8194 - _ 0 0 p4:19:8:1:0
p 13 13 0 0 0 - CSINC 0 SPECIAL/0/0/0/NONE/0/129/-/- 8196 0:REG/8196/0/0/NONE/0/0/-/- REG/8196/0/0/NONE/0/0/-/- 0 0 p4:19:8:2:0
p 14 14 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/1/-/- 8195 - REG/8195/0/0/NONE/0/0/-/- 0 0 p4:18:14:1:0
p 15 15 0 0 0 - CMP 0 REG/8195/0/0/NONE/0/0/-/- 8193 - _ 0 0 p4:18:14:1:0
p 16 16 0 0 0 - BGT 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@11 0 0 p4:18:14:2:0
p 17 17 0 0 0 - MOVD 0 REG/8196/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p4:23:2:1:0
p 18 18 0 0 0 - RET 0 _ 0 - _ 0 0 p4:23:2:2:0
p 19 19 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 16 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 0 MOVD MOVD
spill MEM/8383/0/0/NONE/0/32/-/- 8195 0 MOVB MOVBU
funcaux y3 y4 - - y5 y6 -
needzero -
regargs -
text 0 0 - 0
symalign y3:4,y4:4,y5:1,y6:1
autot -
dbgentry 1
dbgslot 0 n5 t2 0
dbgslot 1 n2 t2 0
dbgslot 2 n4 t3 0
dbgslot 3 n1 t5 0
dbgslot 4 n1 t3 8
dbgslot 5 n1 t3 16
dbgvar 0 n5 0
dbgvar 1 n2 1
dbgvar 2 n4 2
dbgvar 3 n1 3,4,5
dbgloc 0 3:20:3:34:55
dbgloc 1 1:-10000:1:28:53
dbgloc 2 1:39:-1:-30000:50
dbgloc 3 1:-10000:1:39:509308519308529308,1:39:5:25:5093085193089308,5:25:-1:-30000:93085193089308
dbgregout n3
dbgpc 3:20:12,3:34:12,1:28:9,1:39:8,5:25:18
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i32 0 2 p4:16:6:0:0
p 20 0 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/0/y2/- 0 0 p4:16:6:2:0
p 1 4 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p4:16:6:0:0
p 2 4 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p4:16:6:0:0
p 3 4 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p4:16:6:0:0
p 4 4 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y6/- 0 0 p4:16:6:0:0
p 5 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p4:16:6:2:0
p 6 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p4:19:8:1:0
p 7 4 0 0 276 - MOVBU 0 REG/8195/0/0/NONE/2/0/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p4:19:8:1:0
p 8 8 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p4:18:14:1:0
p 9 12 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8196/0/0/NONE/2/0/-/- 0 0 p4:18:14:2:0
p 10 16 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/15/-/@15 0 0 p4:18:14:2:0
p 11 20 0 0 300 - MOVBU 0 MEM/8192/8195/0/NONE/114/0/-/- 0 - REG/8197/0/0/NONE/2/0/-/- 0 0 p4:18:14:2:0
p 12 24 0 0 92 - CMPW 0 REG/8197/0/0/NONE/2/0/-/- 8194 - NONE/0/0/0/NONE/1/0/-/- 0 0 p4:19:8:1:0
p 13 28 0 0 102 - CSINC 0 SPECIAL/0/0/0/NONE/11/129/-/- 8196 0:REG/8196/0/0/NONE/2/0/-/- REG/8196/0/0/NONE/2/0/-/- 0 0 p4:19:8:2:0
p 14 32 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/1/-/- 8195 - REG/8195/0/0/NONE/2/0/-/- 0 0 p4:18:14:1:0
p 15 36 0 0 92 - CMP 0 REG/8195/0/0/NONE/2/0/-/- 8193 - NONE/0/0/0/NONE/1/0/-/- 0 0 p4:18:14:1:0
p 16 40 0 0 80 - BGT 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/11/-/@11 0 0 p4:18:14:2:0
p 17 44 0 0 301 - MOVD 0 REG/8196/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p4:23:2:1:0
p 18 48 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p4:23:2:2:0
fn y1 32 0 0 0 16 2000c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 0 MOVD MOVD
spill MEM/8383/0/0/NONE/0/32/-/- 8195 0 MOVB MOVBU
funcaux y3 y4 - - y5 y6 -
text 64 0 e00700f9621c40d3e3031faae4031faa05000014056863385f00056b8414849a630400913f0003eb6cffff54e00304aac0035fd6000000000000000000000000 0
pcln y11 y12 y13 y14 y7,y8,y9,y10 y3,y4,_,_,_,y5,y6
usedfiles 3
data y3 Sxxx 0 4 8000 02000000010000000100 0
data y4 Sxxx 0 4 8000 0200000000000000 0
data y5 SDATA 11 1 8000 fe000808081008fd1801ff 0
data y6 SDATA 2 1 8000 0000 0
data y7 SRODATA 5 1 28000 0001010f00 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 0 1 28000 - 0
data y10 SRODATA 5 1 28000 0001040f00 0
data y11 SRODATA 3 1 28000 021000 0
data y12 SRODATA 3 1 28000 081000 0
data y13 SRODATA 13 1 28000 220106010104020201030a0500 0
data y14 SRODATA 3 1 28000 001000 0
end
dwarf
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "go:info.[]uint8" 0
sym y20 "go:info.uint8" 0
sym y21 "go:info.int" 0
sym y22 "type:int" 0
dwfn y15 y16 y17 - y18 "internal/bytealg.countGeneric" 3:16 1 0 1 21
dwdcl n1,n2
dwclosure 0 -
dwmark p4:18:2:0:0 1
dwmark p4:22:2:0:0 0
dwparents 0
dwparams n1,n2,n3
dwname n1 1 1 0 0 0 0 0 0 - - "[]uint8" 0 0 1 p4:16:19:0:0
dwname n2 1 1 0 0 0 0 24 0 - - "uint8" 0 0 1 p4:16:29:0:0
dwname n6 1 0 1 0 0 0 0 0 - - "[]uint8" 0 0 1 p4:18:14:0:0
dwname n7 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p4:18:14:0:0
dwname n8 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p4:18:14:0:0
dwname n4 1 0 0 0 0 0 0 0 - - "int" 0 0 1 p4:17:2:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "int" 0 0 1 p4:16:37:0:0
dwname n5 1 0 0 0 0 0 0 0 - - "uint8" 0 0 1 p4:18:9:0:0
var 0 0 "b" 5 1 0 0 0 8 y19 "internal/bytealg/count_native.go" 16 19 0 0 0 0 v3
var 1 0 "c" 5 1 0 0 0 32 y20 "internal/bytealg/count_native.go" 16 29 0 1 0 0 v1
var 2 0 "~r0" 5 1 1 0 0 0 y21 "internal/bytealg/count_native.go" 16 37 0 2 0 0 -
var 3 0 "n" 52 1 0 0 0 -8 y21 "internal/bytealg/count_native.go" 17 2 0 3 0 0 v2
var 4 0 "x" 52 1 0 0 0 -8 y20 "internal/bytealg/count_native.go" 18 9 0 4 0 0 v0
scope 0 0 0:64 0,1,2,3
scope 1 0 4:44 4
data y15 SDWARFFCN 110 0 0 03696e7465726e616c2f62797465616c672e636f756e7447656e65726963000040019c0400000010012d6200001000000000000000002d6300001000000000000000002e7e72300001100000000000276e001100000000000000000c000000002778001200000000000000000000 12
reloc 0 0 R_USETYPE 0 y22
reloc 31 1 R_DWTXTADDR_U1 0 y1
reloc 46 4 R_DWARFSECREF 0 y19
reloc 50 4 R_DWARFSECREF 0 y16
reloc 59 4 R_DWARFSECREF 0 y20
reloc 63 4 R_DWARFSECREF 39 y16
reloc 74 4 R_DWARFSECREF 0 y21
reloc 83 4 R_DWARFSECREF 0 y21
reloc 87 4 R_DWARFSECREF 47 y16
reloc 92 4 R_DWARFSECREF 0 y17
reloc 100 4 R_DWARFSECREF 0 y20
reloc 104 4 R_DWARFSECREF 55 y16
data y16 SDWARFLOC 63 0 0 010004000809509308519308529308040830085093085193089308043040079308519308930800010004000c01530001000408400150000100041818015500 4
reloc 1 1 R_DWTXTADDR_U1 0 y1
reloc 40 1 R_DWTXTADDR_U1 0 y1
reloc 48 1 R_DWTXTADDR_U1 0 y1
reloc 56 1 R_DWTXTADDR_U1 0 y1
data y17 SDWARFRANGE 6 0 0 010004042c00 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y18 SDWARFLINES 39 0 0 0009020000000000000000040406030a14063a360637068806370636065f063c06370210000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG32` gives (`b1`, `b3`, `b2`, `b5`: one entry per value, then the
terminator). -/
def tab : PcTab := [(1, [6, 6, 6, 6, 6, 6, 9, 10, 11]), (3, [12, 13, 13, 14, 15, 16]),
  (2, [16, 16, 16, 17]), (5, [18, 19, 19])]

/-- The class table `checkG32` gives. -/
def kt : KTab := (match checkG32 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk3 : Block := (lc.ctx.f.block? 3).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

def L : Link := Lof ps

def E : MatchEnv := Eof lc ps tab

/-- The flags of `CMPW R5, R2` on `x = c` (`Flags.toValSub`: `N`, `V` clear, `Z`, `C` set, `g`
the sign of `-0`). -/
def fl0 : Val := .agg [.bool false, .bool true, .bool true, .bool false, .bool false]

/-- The `runLoc` state before `v32`: `n = 5` in `R4`, the flags `fl0`, every other register
`poison`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 4 then .int .w64 5 else .poison,
    flags := fl0, slots := [], mem := .mem mem0 }

/-- The machine before `v32`: `X4 = 5`, `NZCV` the flags of `fl0` (`EQ`), the activation's `g`
and `FP`, the PC of `v32`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 4 then 5 else if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8
      else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, true, true, false⟩,
    pc := E.pcOf 3 3, mem := fun _ => 0 }

/-- The register holds the 64-bit integer `5 + 1`. -/
def isRes : Option Val → Bool
  | some (.int .w64 x) => x == 5 + 1
  | _ => false

theorem isRes_spec {o : Option Val} (h : isRes o = true) : o = some (.int .w64 (5 + 1)) := by
  unfold isRes at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on `countGeneric`: it holds an arm64 op, `checkG32` accepts it
with `tab` and `kt` and `checkG30` does not; it accesses no frame variable and has no home slot;
`b3` holds `v32` (`CSINC [NotEqual] v31 v31 v40`) at index 3, `R4` has class 64 before `v32` and
the upper-bit table is empty there; `stepLoc` runs `v32` from `s0` to `R4 = 5 + 1`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG32 lc ps bs g).toOption == some (tab, kt) && (checkG30 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 3 && (lc.ctx.f.block? 3).isSome &&
    (lc.ctx.f.value? 32).isSome && blk3.values[3]? == some 32 && (val 32).op == .ARM64CSINC &&
    (kAt lc kt 3 blk3 3).get 4 == some 64 && uL lc blk3 3 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 32)) fun s1 => isRes s1.regs[4]?

theorem g32c_facts : gFacts = true := by
  native_decide

/-- The facts of `g32c_facts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG32 lc ps bs g = .ok (tab, kt) ∧
      (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 3 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 3 = some blk3 ∧ lc.ctx.f.value? 32 = some (val 32) ∧
      blk3.values[3]? = some 32 ∧ (val 32).op = .ARM64CSINC ∧
      (kAt lc kt 3 blk3 3).get 4 = some 64 ∧ uL lc blk3 3 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 32)) (fun s1 => isRes s1.regs[4]?) = true := by
  have hf := g32c_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hres⟩, -⟩, hav⟩, hsl⟩, hm3⟩, hb3s⟩, hv32s⟩, hi3⟩, hop⟩, hk4⟩, hu⟩,
    hrun⟩ := hf
  refine ⟨hl, ?_, hav, hsl, hm3, ?_, ?_, hi3, hop, hk4, hu, hrun⟩
  · revert hres; cases checkG32 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb3s
    simp [blk3, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv32s
    simp [val, hv]

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 4 ∧ x = .int .w64 5) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h4; exact Or.inl ⟨h4, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 3 3 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl rfl
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := ⟨rfl, rfl, rfl, rfl⟩
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E, Eof]; decide,
    by simp only [MState.word, readMem, m0, E, Eof]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g32cInv0 (h4 : (kAt lc kt 3 blk3 3).get 4 = some 64) :
    G3Inv E lc (kAt lc kt 3 blk3 3) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h4] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v32`, the `CSINC`: none apply. -/
theorem pre32 {s : LocState} (hop : (val 32).op = .ARM64CSINC) : G14Pre lc s (val 32) := by
  have hne : ∀ o : Op, o ≠ .ARM64CSINC → (val 32).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G32's `CSINC` on `internal/bytealg.countGeneric`**: from the state before `v32` with `n = 5`
in `R4` (`X4 = 5`) and the flags of `CMPW R5, R2` on `x = c` (`NZCV = 0b0110`, `EQ`), `g32_value`
runs `CSINC NE, R4, R4, R4` (`v32`): `NE` fails, so `runLoc`'s `R4` holds `5 + 1` (the `y + 1`
branch, `n++`) and the machine state, related to it before `v27` under an activation extending
`E` that is again a `G28Env`, has `X4 = 5 + 1`. -/
theorem genG32_csinc_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 32) = .ok s1 ∧
      s1.regs[4]? = some (.int .w64 (5 + 1)) ∧
      E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E1 s1 3 4 m1 ∧ m1.x 4 = 5 + 1 := by
  obtain ⟨hl, hc, hav, hsl, hm3, hb, hv32, hi3, hop, hk4, hu, hrun⟩ := facts
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hr1' := isRes_spec hr1
  have hE : G28Env lc g L ps 0 tab E := envOf hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64CSINC → (val 32).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g32_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm3 hb hi3 hv32 (by rw [hop]; rfl) locMatch0 (g32cInv0 hk4)
    (by rw [hu]; intro e he; cases he) (pre32 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  exact ⟨s1, E1, m1, hs1, hr1', hx1, hE1, hp1, hm1',
    valRel_i64 hA ((hm1'.regs 4 _ hr1').1 4 rfl)⟩

end GoFV.Proof.Witness.GenG32c
