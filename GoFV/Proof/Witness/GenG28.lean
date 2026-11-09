import GoFV.Proof.Gen.G28
import GoFV.Proof.Witness.GenG13
import GoFV.Proof.Witness.GenG27

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G28 of the genssa validator on `runtime.envKeyEqual`

`std/std/runtime/envKeyEqual,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`):

```go
func envKeyEqual(a, b string) bool {
	if GOOS == "windows" { … }
	return a == b
}
```

`checkG27` rejects it (`v24: op LoweredMemEq`); `checkG28` accepts it with the PC table `tab` and
the class table `kt`. Block `b2` (the lengths agree) moves the arguments into place
(`v14 = Copy v18`, `v22 = Copy v17`, `v23 = Copy v14`) and runs
`v24 = LoweredMemEq v20 v22 v23 v1` (`CALL runtime.memequal(SB)`), whose result `b3` returns.

The runtime `Hm` implements `runtime.memequal` on the machine: it compares the `X2` bytes at `X0`
and at `X1` and returns 1 or 0 in `X0` to `X30`. It satisfies the trusted contract `MemEqOK` at
`v24` (`memEqOK0`). By compiled evaluation (`native_decide`, listed in
`scripts/axioms-allowlist.txt`; `g28_facts`), `stepLoc` runs `v24` from a state with `a` the
start of `heap 1` (`GenG13.pB`) in `R0`, `b` 8 bytes into it in `R1`, the length 8 in `R2` and
`heap 1` 64 bytes 7 (`GenG13.mem7`): the bytes agree and `R0` then holds `true`. On a framed
activation with `G28Env` with `heap 1` at `GenG13.A` (`GenG13.M7`), `g28_value` runs the `CALL`
and the hook: the machine's `X0` is 1 (`genG28_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG28

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/envKeyEqual,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "envKeyEqual" 1 0 0
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
type t2 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t1 FUNC 8 8 8 hasptr,direct "func(string, string) bool" "func(string, string) bool" 0 2 1
field 0 "a" t2 ? 0
field 1 "b" t2 ? 0
field 2 "" t3 ? 0
aux a2 sym "runtime.envKeyEqual" "runtime.envKeyEqual" 1 - 0 - - - - 0
posbase p124 "runtime/env_posix.go" 1 1 -1
aux a3 name "a" "a" PPARAM t2 0 1 used p124:24:18:0:0
aux a4 name "b" "b" PPARAM t2 16 1 used p124:24:21:0:0
aux a5 name "~r0" "~r0" PPARAMOUT t3 0 1 - p124:24:31:0:0
aux a1 call "AuxCall{runtime.envKeyEqual}" a2 1 2 1 8 32 4 1
abiparam in 0 t2 a3 0,1 0
abiparam in 1 t2 a4 2,3 16
abiparam out 0 t3 a5 0 -1
type t4 INT8 1 1 0 comparable,named "int8" "int8"
type t5 INT16 2 2 0 comparable,named "int16" "int16"
type t6 INT32 4 4 0 comparable,named "int32" "int32"
type t7 INT64 8 8 0 comparable,named "int64" "int64"
type t8 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t9 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t10 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t11 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t12 INT 8 8 0 comparable,named "int" "int"
type t13 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t14 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t15 UINT 8 8 0 comparable,named "uint" "uint"
type t16 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t12
type t21 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t16
type t22 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t13
type t23 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t14
type t24 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t17
type t25 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t26 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t27 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t28 SSA ? ? ? - "mem" ""
type t29 SSA ? ? ? - "flags" ""
type t30 SSA ? ? ? - "void" ""
type t31 SSA 16 8 ? - "int128" ""
type t32 RESULTS ? ? ? - "mem" "" 1 t28
type t33 PTR 8 8 8 hasptr,direct,comparable "*string" "*string" t2
type t34 PTR 8 8 8 hasptr,direct,comparable "*bool" "*bool" t3
type t35 RESULTS ? ? ? - "bool,mem" "" 2 t3,t28
slot s1 a3 t2 0 - 0
slot s2 a4 t2 0 - 0
f b1 t1 a1 27 3
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t14,UInt=t15,Uintptr=t16,String=t2,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t34 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p124:24:6:2:0 2 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v9 ConstBool t3 0 - p0:0:0:0:0 0 -
v v10 StringLen t12 0 - p124:35:11:0:0 1 v7
v v11 Copy t16 0 - p124:35:11:2:0 1 v10
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v13 Copy t16 0 - p124:35:11:2:0 1 v12
v v14 Eq64 t3 0 - p124:35:11:0:0 2 v11,v13
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v15 Copy t2 0 - p124:35:11:2:0 2 v7
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v15
v v17 Copy t27 0 - p124:35:11:2:0 1 v16
v v18 Copy t2 0 - p124:35:11:2:0 1 v8
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v18
v v20 Copy t27 0 - p124:35:11:2:0 1 v19
v v21 StringLen t12 0 - p124:35:11:0:0 1 v15
v v22 Copy t16 0 - p124:35:11:2:0 1 v21
v v23 Copy t28 0 - p124:35:11:2:0 2 v1
v v24 MemEq t3 0 - p124:35:11:0:0 1 v17,v20,v22,v23
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v14,v24
v v26 Phi t28 0 - p124:35:11:0:0 1 v1,v23
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v26
names s1,s2
named s1 v7,v15
named s2 v8,v18
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t34 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p124:24:6:2:0 2 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v9 ConstBool t3 0 - p0:0:0:0:0 0 -
v v10 StringLen t12 0 - p124:35:11:1:0 1 v7
v v11 Copy t16 0 - p124:35:11:2:0 1 v10
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v13 Copy t16 0 - p124:35:11:2:0 1 v12
v v14 Eq64 t3 0 - p124:35:11:0:0 2 v11,v13
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v15 Copy t2 0 - p124:35:11:2:0 2 v7
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v15
v v17 Copy t27 0 - p124:35:11:2:0 1 v16
v v18 Copy t2 0 - p124:35:11:2:0 1 v8
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v18
v v20 Copy t27 0 - p124:35:11:2:0 1 v19
v v21 StringLen t12 0 - p124:35:11:0:0 1 v15
v v22 Copy t16 0 - p124:35:11:2:0 1 v21
v v23 Copy t28 0 - p124:35:11:2:0 2 v1
v v24 MemEq t3 0 - p124:35:11:0:0 1 v17,v20,v22,v23
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v14,v24
v v26 Phi t28 0 - p124:35:11:0:0 1 v1,v23
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v26
names s1,s2
named s1 v7,v15
named s2 v8,v18
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9
freev -
freeb -
cache postorder b3,b2,b1
cache linestarts 124:35:35
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t34 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p124:24:6:2:0 4 -
v v8 Arg t2 0 a4 p124:24:6:2:0 3 -
v v9 ConstBool t3 0 - p0:0:0:0:0 0 -
v v10 StringLen t12 0 - p124:35:11:1:0 2 v7
v v11 Copy t16 0 - p124:35:11:2:0 0 v10
v v12 StringLen t12 0 - p124:35:11:0:0 2 v8
v v13 Copy t16 0 - p124:35:11:2:0 0 v12
v v14 Eq64 t3 0 - p124:35:11:0:0 2 v10,v12
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v15 Copy t2 0 - p124:35:11:2:0 0 v7
v v16 StringPtr t17 0 - p124:35:11:0:0 2 v7
v v17 Copy t27 0 - p124:35:11:2:0 0 v16
v v18 Copy t2 0 - p124:35:11:2:0 0 v8
v v19 StringPtr t17 0 - p124:35:11:0:0 2 v8
v v20 Copy t27 0 - p124:35:11:2:0 0 v19
v v21 StringLen t12 0 - p124:35:11:0:0 2 v7
v v22 Copy t16 0 - p124:35:11:2:0 0 v21
v v23 Copy t28 0 - p124:35:11:2:0 0 v1
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v21,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v14,v24
v v26 Copy t28 0 - p124:35:11:0:0 0 v1
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7,v7
named s2 v8,v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9
freev -
freeb -
cache postorder b3,b2,b1
cache linestarts 124:35:35
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 3 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v10 StringLen t12 0 - p124:35:11:1:0 1 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 2 v10,v12
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v21 StringLen t12 0 - p124:35:11:0:0 1 v7
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v21,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v14,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v26,v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 124:35:35
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 3 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v10 StringLen t12 0 - p124:35:11:1:0 1 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v21 StringLen t12 0 - p124:35:11:0:0 1 v7
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v21,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 124:35:35
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 3 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v10 StringLen t12 0 - p124:35:11:1:0 1 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v21 StringLen t12 0 - p124:35:11:0:0 1 v7
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v21,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 124:35:35
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 3 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v10 StringLen t12 0 - p124:35:11:1:0 1 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v21 StringLen t12 0 - p124:35:11:0:0 1 v7
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v21,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 124:35:35
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 3 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v10 StringLen t12 0 - p124:35:11:1:0 1 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v21 StringLen t12 0 - p124:35:11:0:0 1 v7
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v21,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 124:35:35
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 3 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v10 StringLen t12 0 - p124:35:11:1:0 1 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v21 StringLen t12 0 - p124:35:11:0:0 1 v7
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v21,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 124:35:35
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 3 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v10 StringLen t12 0 - p124:35:11:1:0 1 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v21 StringLen t12 0 - p124:35:11:0:0 1 v7
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v21,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 124:35:35
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 3 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v10 StringLen t12 0 - p124:35:11:1:0 2 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v21 StringLen t12 0 - p124:35:11:0:0 0 v7
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v10,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 3 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v10 StringLen t12 0 - p124:35:11:1:0 2 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v21 StringLen t12 0 - p124:35:11:0:0 0 v7
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v10,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 2 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v10 StringLen t12 0 - p124:35:11:1:0 2 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v10,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v21,v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 2 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v10 StringLen t12 0 - p124:35:11:1:0 2 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v10,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v21,v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 2 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v10 StringLen t12 0 - p124:35:11:1:0 2 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v10,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v21,v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 2 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v10 StringLen t12 0 - p124:35:11:1:0 2 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v10,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v21,v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 2 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v10 StringLen t12 0 - p124:35:11:1:0 2 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v10,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v21,v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 2 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v10 StringLen t12 0 - p124:35:11:1:0 2 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v10,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v21,v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 2 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v10 StringLen t12 0 - p124:35:11:1:0 2 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v10,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v21,v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p124:24:6:2:0 2 -
v v8 Arg t2 0 a4 p124:24:6:2:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v10 StringLen t12 0 - p124:35:11:1:0 2 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v10,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v21,v23,v22,v20,v18,v17,v15,v13,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 20 "expand calls"
aux a6 nameoff "a+0" a3 0
aux a7 nameoff "a+8" a3 8
aux a8 nameoff "b+0" a4 0
aux a9 nameoff "b+8" a4 8
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 StringMake t2 0 - p124:35:11:2:0 2 v20,v18
v v8 StringMake t2 0 - p124:35:11:2:0 2 v17,v15
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v10 StringLen t12 0 - p124:35:11:1:0 2 v7
v v12 StringLen t12 0 - p124:35:11:0:0 1 v8
v v14 Eq64 t3 0 - p124:35:11:0:0 1 v10,v12
v v21 SB t16 0 - p0:0:0:0:0 0 -
v v23 SP t16 0 - p0:0:0:0:0 2 -
v v22 OffPtr t33 0 - p0:0:0:0:0 0 v23
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 1 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v16 StringPtr t17 0 - p124:35:11:0:0 1 v7
v v19 StringPtr t17 0 - p124:35:11:0:0 1 v8
v v24 MemEq t3 0 - p124:35:11:0:0 1 v16,v19,v10,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
v v13 LocalAddr t34 0 a5 p124:35:2:0:0 0 v23,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26,v22
freev v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 21 "decompose builtin"
slot s3 a3 t17 0 - 0
slot s4 a3 t12 8 - 0
slot s5 a4 t17 0 - 0
slot s6 a4 t12 8 - 0
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 StringMake t2 0 - p124:35:11:2:0 0 v20,v18
v v8 StringMake t2 0 - p124:35:11:2:0 0 v17,v15
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v14 Eq64 t3 0 - p124:35:11:1:0 1 v18,v15
v v21 SB t16 0 - p0:0:0:0:0 0 -
v v23 SP t16 0 - p0:0:0:0:0 2 -
v v22 OffPtr t33 0 - p0:0:0:0:0 0 v23
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 2 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 3 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 2 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 2 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 MemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
v v13 LocalAddr t34 0 a5 p124:35:2:0:0 0 v23,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26,v22
freev v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 StringMake t2 0 - p124:35:11:2:0 0 v20,v18
v v8 StringMake t2 0 - p124:35:11:2:0 0 v17,v15
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v14 Eq64 t3 0 - p124:35:11:1:0 1 v18,v15
v v21 SB t16 0 - p0:0:0:0:0 0 -
v v23 SP t16 0 - p0:0:0:0:0 2 -
v v22 OffPtr t33 0 - p0:0:0:0:0 0 v23
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 2 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 3 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 2 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 2 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 MemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
v v13 LocalAddr t34 0 a5 p124:35:2:0:0 0 v23,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26,v22
freev v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 StringMake t2 0 - p124:35:11:2:0 0 v20,v18
v v8 StringMake t2 0 - p124:35:11:2:0 0 v17,v15
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v14 Eq64 t3 0 - p124:35:11:1:0 1 v18,v15
v v21 SB t16 0 - p0:0:0:0:0 0 -
v v23 SP t16 0 - p0:0:0:0:0 2 -
v v22 OffPtr t33 0 - p0:0:0:0:0 0 v23
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 2 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 3 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 2 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 2 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 MemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
v v13 LocalAddr t34 0 a5 p124:35:2:0:0 0 v23,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26,v22
freev v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v14 Eq64 t3 0 - p124:35:11:1:0 1 v18,v15
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 MemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v13,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v14 Eq64 t3 0 - p124:35:11:1:0 1 v18,v15
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 MemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v13,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v14 Eq64 t3 0 - p124:35:11:1:0 1 v18,v15
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 MemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v13,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v14 Eq64 t3 0 - p124:35:11:1:0 1 v18,v15
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 MemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v13,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v14 Eq64 t3 0 - p124:35:11:1:0 1 v18,v15
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 MemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v13,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v14 Eq64 t3 0 - p124:35:11:1:0 1 v18,v15
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 MemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v13,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v14 Eq64 t3 0 - p124:35:11:1:0 1 v18,v15
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 MemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v13,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v14 Eq64 t3 0 - p124:35:11:1:0 1 v18,v15
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 MemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v13,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 27 3
b b1 If p124:35:11:0:0 0 0 - v14 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ConstBool t3 0 - p0:0:0:0:0 1 -
v v14 Eq64 t3 0 - p124:35:11:1:0 1 v18,v15
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 MemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v26
freev v13,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 33 "lower"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64MOVDconst t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64MOVDconst t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 36 "pair"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3
cache linestarts 124:35:35
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 27 3
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b1:1,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 27 4
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b4:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b4:0,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
b b4 Plain p124:35:11:0:0 0 0 - - b3:0 b1:1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 27 4
b b1 ARM64EQ p124:35:11:0:0 0 0 - v13 b2:0,b4:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b4:0,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
b b4 Plain p124:35:11:0:0 0 0 - - b3:0 b1:1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 27 4
b b1 ARM64EQ p124:35:11:0:0 -1 0 - v13 b2:0,b4:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b4:0,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
b b4 Plain p124:35:11:0:0 0 0 - - b3:0 b1:1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:b3:11:14,b3:b1:-:-:17:20,b4:b1:-:b2:5:8
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 27 4
b b1 ARM64EQ p124:35:11:0:0 -1 0 - v13 b2:0,b4:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b4 Plain p124:35:11:0:0 0 0 - - b3:0 b1:1
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b4:0,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 27 4
b b1 ARM64EQ p124:35:11:0:0 -1 0 - v13 b2:0,b4:0 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b4 Plain p124:35:11:0:0 0 0 - - b3:0 b1:1
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b4:0,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 27 4
b b1 ARM64EQ p124:35:11:0:0 -1 0 - v13 b2:0,b4:0 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b4 Plain p124:35:11:0:0 0 0 - - b3:0 b1:1
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b4:0,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 27 4
b b1 ARM64EQ p124:35:11:0:0 -1 0 - v13 b2:0,b4:0 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b4 Plain p124:35:11:0:0 0 0 - - b3:0 b1:1
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v17,v18,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b4:0,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v26,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v14,v22,v23,v21,v8,v7,v19,v16,v12,v10,v11,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.envKeyEqual}" a2 1 2 1 8 32 4 1
abiparam in 0 t2 a3 0,1 0
abiparam in 1 t2 a4 2,3 16
abiparam out 0 t3 a5 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 27 4
b b1 ARM64EQ p124:35:11:0:0 -1 0 - v13 b2:0,b4:0 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b4 Plain p124:35:11:0:0 0 0 - - b3:0 b1:1
v v21 Copy t3 0 - p124:35:11:2:0 1 v26
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v14 Copy t12 0 - p124:35:11:2:0 1 v18
v v22 Copy t17 0 - p124:35:11:2:0 1 v17
v v23 Copy t12 0 - p124:35:11:2:0 1 v14
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v22,v23,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b4:0,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v21,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v16,v19
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
fstate scheduled,laidout
regalloc 28 v14:R3,v15:R3,v17:R2,v18:R1,v20:R0,v21:R0,v22:R1,v23:R2,v24:R0,v25:R0,v26:ZERO,v27:[]
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 27 4
b b1 ARM64EQ p124:35:11:0:0 -1 0 - v13 b2:0,b4:0 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b4 Plain p124:35:11:0:0 0 0 - - b3:0 b1:1
v v21 Copy t3 0 - p124:35:11:2:0 1 v26
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v14 Copy t12 0 - p124:35:11:2:0 1 v18
v v22 Copy t17 0 - p124:35:11:2:0 1 v17
v v23 Copy t12 0 - p124:35:11:2:0 1 v14
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v22,v23,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b4:0,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v21,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v16,v19
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
fstate scheduled,laidout
regalloc 28 v14:R3,v15:R3,v17:R2,v18:R1,v20:R0,v21:R0,v22:R1,v23:R2,v24:R0,v25:R0,v26:ZERO,v27:[]
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 27 4
b b1 ARM64EQ p124:35:11:0:0 -1 0 - v13 b2:0,b4:0 -
v v18 ArgIntReg t12 1 a7 p124:35:11:2:0 2 -
v v15 ArgIntReg t12 3 a9 p124:35:11:2:0 1 -
v v20 ArgIntReg t17 0 a6 p124:35:11:2:0 1 -
v v17 ArgIntReg t17 2 a8 p124:35:11:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v26 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64CMP t29 0 - p124:35:11:1:0 1 v18,v15
b b4 Plain p124:35:11:0:0 0 0 - - b3:0 b1:1
v v21 Copy t3 0 - p124:35:11:2:0 1 v26
b b2 Plain p124:35:11:0:0 0 0 - - b3:1 b1:0
v v14 Copy t12 0 - p124:35:11:2:0 1 v18
v v22 Copy t17 0 - p124:35:11:2:0 1 v17
v v23 Copy t12 0 - p124:35:11:2:0 1 v14
v v24 ARM64LoweredMemEq t3 0 - p124:35:11:0:0 1 v20,v22,v23,v1
b b3 Ret p124:35:11:1:0 0 0 - v27 - b4:0,b2:0
v v25 Phi t3 0 - p124:35:11:0:0 1 v21,v24
v v27 MakeResult t35 0 - p124:35:2:0:0 1 v25,v1
names s3,s4,s5,s6
named s3 v20
named s4 v18
named s5 v17
named s6 v15
splits s1/0/t17=s3,s1/8/t12=s4,s2/0/t17=s5,s2/8/t12=s6
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v16,v19
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5,a8:6,a9:7
cache linestarts 124:35:35
fstate scheduled,laidout
regalloc 28 v14:R3,v15:R3,v17:R2,v18:R1,v20:R0,v21:R0,v22:R1,v23:R2,v24:R0,v25:R0,v26:ZERO,v27:[]
dcllen 3
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t21,t24,t25,t26,t27,t33
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t12,t15,t16,t25,t26,t13,t14,t3,t17,t18,t19,t20,t21,t22,t23,t34,t24,t33,t1,t2,t27,t28,t30,t29,t31,t32,t35
eof
"#

/-- `std/std/runtime/envKeyEqual,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "envKeyEqual" 1
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
type t1 16 8 8 1 01 "string"
name n1 "a" PPARAM t1 1 "runtime.a" 0 a3
name n2 "b" PPARAM t1 1 "runtime.b" 0 a4
type t2 1 1 0 0 - "bool"
name n3 "~r0" PPARAMOUT t2 1 "runtime.~r0" 0 a5
in n1 0 used
in n2 16 used
in n3 0 outregs
out n1 0 used
out n2 16 used
opt n3 0 outregs
stack 0 0 8
end
genin
posbase p124 "runtime/env_posix.go" 1 1 -1 121 "runtime/env_posix.go" "runtime/env_posix.go" 1 1
type t3 8 8 8 1 01 "*uint8"
type t4 8 8 0 0 - "int"
sym y1 "runtime.envKeyEqual" 1
curfn p124:24:6:0:0 0 0
regargs 8192:0:t3,8193:8:t4,8194:16:t3,8195:24:t4
text y1 0 0 0 0 24 201080
end
prog0
sym y2 "runtime.a" 0
sym y3 "runtime.b" 0
sym y4 "gclocals\xc2\xb7itaneJMpbAudh9zNu5JnHA==" 0
sym y5 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y6 "runtime.envKeyEqual.arginfo1" 0
sym y7 "runtime.envKeyEqual.argliveinfo" 0
sym y8 "runtime.memequal" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i32 0 0 p124:24:6:0:0
p 18 18 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/PARAM/0/0/y2/- 0 0 p124:24:6:2:0
p 19 19 0 0 0 - MOVD 0 REG/8194/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/PARAM/0/16/y3/- 0 0 p124:24:6:2:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p124:24:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p124:24:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p124:24:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p124:24:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p124:24:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p124:35:11:1:0
p 7 7 0 0 0 - CMP 0 REG/8195/0/0/NONE/0/0/-/- 8193 - _ 0 0 p124:35:11:1:0
p 8 8 0 0 0 - BEQ 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@11 0 0 p124:35:11:2:0
p 9 9 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p124:35:11:2:0
p 10 10 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@16 0 0 p124:35:11:2:0
p 11 11 0 0 0 - MOVD 0 REG/8193/0/0/NONE/0/0/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p124:35:11:2:0
p 12 12 0 0 0 - MOVD 0 REG/8194/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p124:35:11:2:0
p 13 13 0 0 0 - MOVD 0 REG/8195/0/0/NONE/0/0/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p124:35:11:2:0
p 14 14 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p124:35:11:2:0
p 15 15 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y8/- 0 0 p124:35:11:2:0
p 16 16 0 0 0 - RET 0 _ 0 - _ 0 0 p124:35:11:1:0
p 17 17 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 24 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 8195 STP LDP
funcaux y4 y5 - - y6 y7 -
needzero -
regargs -
text 0 0 - 0
symalign y4:4,y5:4,y6:1,y7:1
autot -
dbgentry 1
dbgslot 0 n1 t3 0
dbgslot 1 n1 t4 8
dbgslot 2 n2 t3 0
dbgslot 3 n2 t4 8
dbgvar 0 n1 0,1
dbgvar 1 n2 2,3
dbgloc 0 1:-10000:4:21:509308519308,4:21:2:22:9308519308,2:22:2:24:5093089308
dbgloc 1 1:-10000:2:14:529308539308,2:14:2:23:5293089308
dbgregout n3
dbgpc 4:21:10,2:22:13,2:24:16,2:14:12,2:23:14
end
asm
sym y9 "runtime.morestack_noctxt" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i32 0 0 p124:24:6:0:0
p 20 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p124:24:6:0:0
p 21 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p124:24:6:0:0
p 22 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p124:24:6:0:0
p 23 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@32 0 0 p124:24:6:0:0
p 24 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p124:24:6:0:0
p 25 12 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p124:24:6:0:1
p 26 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p124:24:6:0:0
p 27 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p124:24:6:0:0
p 18 24 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/0/y2/- 0 0 p124:24:6:2:0
p 19 28 0 0 304 - MOVD 0 REG/8194/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/16/y3/- 0 0 p124:24:6:2:0
p 1 32 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p124:24:6:0:0
p 2 32 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p124:24:6:0:0
p 3 32 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y6/- 0 0 p124:24:6:0:0
p 4 32 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y7/- 0 0 p124:24:6:0:0
p 5 32 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p124:24:6:2:0
p 6 32 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p124:35:11:1:0
p 7 32 0 0 92 - CMP 0 REG/8195/0/0/NONE/2/0/-/- 8193 - NONE/0/0/0/NONE/1/0/-/- 0 0 p124:35:11:1:0
p 8 36 0 0 80 - BEQ 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/11/-/@11 0 0 p124:35:11:2:0
p 9 40 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p124:35:11:2:0
p 10 44 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/16/-/@16 0 0 p124:35:11:2:0
p 11 48 0 0 301 - MOVD 0 REG/8193/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p124:35:11:2:0
p 12 52 0 0 301 - MOVD 0 REG/8194/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p124:35:11:2:0
p 13 56 0 0 301 - MOVD 0 REG/8195/0/0/NONE/2/0/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p124:35:11:2:0
p 14 60 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p124:35:11:2:0
p 15 60 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y8/- 0 0 p124:35:11:2:0
p 16 64 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p124:35:11:1:0
p 28 68 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p124:35:11:1:0
p 29 72 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p124:35:11:1:0
p 30 76 -16 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p124:35:11:1:0
p 31 76 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p124:24:6:0:0
p 32 76 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p124:24:6:0:0
p 33 76 0 0 436 - STP 0 REGREG/8192/0/0/NONE/7/8193/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p124:24:6:0:0
p 34 80 0 0 436 - STP 0 REGREG/8194/0/0/NONE/7/8195/-/- 0 - MEM/8383/0/0/NONE/87/24/-/- 0 0 p124:24:6:0:0
p 35 84 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p124:24:6:0:0
p 36 88 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y9/- 0 0 p124:24:6:0:0
p 37 92 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p124:24:6:0:0
p 38 92 0 0 245 - LDP 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REGREG/8192/0/0/NONE/7/8193/-/- 0 0 p124:24:6:0:0
p 39 96 0 0 245 - LDP 0 MEM/8383/0/0/NONE/87/24/-/- 0 - REGREG/8194/0/0/NONE/7/8195/-/- 0 0 p124:24:6:0:0
p 40 100 16 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@20 0 0 p124:24:6:0:0
fn y1 32 8 0 0 24 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 8195 STP LDP
funcaux y4 y5 - - y6 y7 -
text 112 0 900b40f9ff6330eb29020054fe0f1ff8fd831ff8fd2300d1e00f00f9e21700f93f0003eb60000054e0031faa05000014e30301aae10302aae20303aa00000094fd835ff8fe0741f8c0035fd6e08700a9e28f01a9e3031eaa00000094e08740a9e28f41a9e7ffff170000000000000000 2
reloc 60 4 R_CALLARM64 0 y8
reloc 88 4 R_CALLARM64 0 y9
pcln y14 y15 y16 y17 y10,y11,y12,y13 y4,y5,_,_,_,y6,y7
usedfiles 121
data y4 Sxxx 0 4 8000 02000000030000000500 0
data y5 Sxxx 0 4 8000 0200000000000000 0
data y6 SDATA 13 1 8000 fe00080808fdfe10081808fdff 0
data y7 SDATA 2 1 8000 0000 0
data y10 SRODATA 11 1 28000 000101020205010f020500 0
data y11 SRODATA 7 1 28000 000f0404030900 0
data y12 SRODATA 0 1 28000 - 0
data y13 SRODATA 5 1 28000 0008041400 0
data y14 SRODATA 7 1 28000 0204200e1f0a00 0
data y15 SRODATA 4 1 28000 f4011c00 0
data y16 SRODATA 7 1 28000 3208160b150900 0
data y17 SRODATA 3 1 28000 001c00 0
end
dwarf
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
sym y21 "go:info.runtime.envKeyEqual$abstract" 0
sym y22 "" 0
sym y23 "go:info.string" 0
sym y24 "go:info.bool" 0
sym y25 "type:bool" 0
dwfn y18 y19 y20 y21 y22 "runtime.envKeyEqual" 121:24 1 0 1 4262
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2,n3
dwprecursor y1 y21 n1,n2,n3
dwname n1 1 1 0 0 0 0 0 0 - - "string" 0 0 1 p124:24:18:0:0
dwname n2 1 1 0 0 0 0 16 0 - - "string" 0 0 1 p124:24:21:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "bool" 0 0 1 p124:24:31:0:0
var 0 0 "a" 5 1 0 0 0 8 y23 "runtime/env_posix.go" 24 18 0 0 1 0 v0
var 1 0 "b" 5 1 0 0 0 24 y23 "runtime/env_posix.go" 24 21 0 1 1 0 v1
var 2 0 "~r0" 5 1 1 0 0 0 y24 "runtime/env_posix.go" 24 31 0 2 0 0 -
scope 0 0 - 0,1,2
dieref y18 3 y21 0
dieref y18 5 y21 1
dieoff y21 0:24,1:32
data y18 SDWARFFCN 41 0 0 0600000000000070019c2900000000000000002900000000000000002e7e7230000118000000000000 8
reloc 0 0 R_USETYPE 0 y25
reloc 1 4 R_DWARFSECREF 0 y21
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y21
reloc 15 4 R_DWARFSECREF 0 y19
reloc 20 4 R_DWARFSECREF 0 y21
reloc 24 4 R_DWARFSECREF 32 y19
reloc 35 4 R_DWARFSECREF 0 y24
data y19 SDWARFLOC 55 0 0 01000004002c06509308519308042c38059308519308043840055093089308000100000400340652930853930804343c05529308930800 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 33 2 R_DWTXTADDR_U2 0 y1
data y20 SDWARFRANGE 0 0 0 - 0
data y22 SDWARFLINES 37 0 0 0009020000000000000000047a0312140a8706870603066406370608370379830224000101 1
reloc 3 8 R_ADDR 0 y1
data y21 SDWARFABSFCN 41 0 1 0572756e74696d652e656e764b6579457175616c000118012261000000000000226200000000000000 2
reloc 28 4 R_DWARFSECREF 0 y23
reloc 36 4 R_DWARFSECREF 0 y23
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

/-- The PC table `checkG28` gives (`b1`, `b4`, `b2`, `b3`: one entry per value, then the
terminator). -/
def tab : PcTab := [(1, [7, 7, 7, 7, 7, 7, 7, 10]), (4, [11, 12]), (2, [13, 14, 15, 16, 18]),
  (3, [18, 18, 18])]

/-- The class table `checkG28` gives. -/
def kt : KTab := (match checkG28 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk2 : Block := (lc.ctx.f.block? 2).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `GenG13.A` and the PC table of `checkG28`. -/
def E : MatchEnv :=
  { lc, ι := GenG13.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The argument `b`: 8 bytes into `heap 1`. -/
def pQ : Ptr := ⟨.heap 1, 8⟩

/-- The `runLoc` state before `v24`: `a` (`GenG13.pB`) in `R0`, `b` (`pQ`) in `R1`, the length 8
in `R2`, every other register `poison`, the memory `GenG13.mem7`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG13.mem7 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 0 then .ptr GenG13.pB else if i.val = 1 then .ptr pQ
      else if i.val = 2 then .int .w64 8 else .poison,
    flags := .poison, slots := [], mem := .mem GenG13.mem7 }

/-- The machine before `v24`: `X0` the address `A` of `a`, `X1 = A + 8`, `X2 = 8`, the
activation's `g` and `FP`, the PC of `v24`, the memory `GenG13.M7`. -/
def m0 : MState :=
  { x := fun k => if k = 0 then GenG13.A else if k = 1 then GenG13.A + 8 else if k = 2 then 8
      else if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 2 3, mem := GenG13.M7 }

/-- `runtime.memequal` on the machine: whether the `X2` bytes at `X0` and at `X1` agree. -/
def memeqW (m : MState) : Bool :=
  (List.range (m.x 2).toNat).all fun i =>
    m.mem (m.x 0 + BitVec.ofNat 64 i) == m.mem (m.x 1 + BitVec.ofNat 64 i)

/-- A runtime whose every entry point is `runtime.memequal`: 1 or 0 in `X0` (`memeqW`), return to
`X30`, every other register and the memory kept. -/
def Hm : Hooks := ⟨fun m => some (.ret { m with
  x := fun k => if k = 0 then (if memeqW m then 1 else 0) else m.x k, pc := m.x 30 })⟩

/-- The value is `true`. -/
def isTrue : Val → Bool
  | .bool b => b
  | _ => false

theorem isTrue_spec {x : Val} (h : isTrue x = true) : x = .bool true := by
  unfold isTrue at h
  split at h
  · rw [h]
  · cases h

/-- The register holds `true`. -/
def isTrueR (o : Option Val) : Bool := (o.map isTrue).getD false

theorem isTrueR_spec {o : Option Val} (h : isTrueR o = true) : o = some (.bool true) := by
  unfold isTrueR at h
  cases o with
  | none => cases h
  | some x => rw [isTrue_spec h]

/-- What compiled evaluation checks on `envKeyEqual`: it holds an arm64 op, `checkG28` accepts it
with `tab` and `kt` and `checkG27` does not; it accesses no frame variable and has no home slot;
`b2` holds `v24` (`LoweredMemEq v20 v22 v23 v1`) at index 3, `R0`, `R1`, `R2` have class 64
before it and nothing is in the upper-bit table there; `memEq` of what `v20`, `v22`, `v23` read
in `s0` and of `GenG13.mem7` is `true`, and so is `memeqW m0`; `stepLoc` runs `v24` from `s0` to
`R0 = true`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG28 lc ps bs g).toOption == some (tab, kt) && (checkG27 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 2 && (lc.ctx.f.block? 2).isSome &&
    (lc.ctx.f.value? 24).isSome && blk2.values[3]? == some 24 &&
    (val 24).op == .ARM64LoweredMemEq && (val 24).args == #[20, 22, 23, 1] &&
    (kAt lc kt 2 blk2 3).get 0 == some 64 && (kAt lc kt 2 blk2 3).get 1 == some 64 &&
    (kAt lc kt 2 blk2 3).get 2 == some 64 && uAt lc blk2 3 == none &&
    GenG1.okThen (s0.read lc 20) (fun p => GenG1.okThen (s0.read lc 22) fun q =>
      GenG1.okThen (s0.read lc 23) fun n => isTrue (memEq [p, q, n, .mem GenG13.mem7])) &&
    memeqW m0 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 24)) fun s1 => isTrueR s1.regs[0]?

theorem g28_facts : gFacts = true := by
  native_decide

/-- The facts of `g28_facts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG28 lc ps bs g = .ok (tab, kt) ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      2 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 2 = some blk2 ∧
      lc.ctx.f.value? 24 = some (val 24) ∧ blk2.values[3]? = some 24 ∧
      (val 24).op = .ARM64LoweredMemEq ∧ (val 24).args = #[20, 22, 23, 1] ∧
      (kAt lc kt 2 blk2 3).get 0 = some 64 ∧ (kAt lc kt 2 blk2 3).get 1 = some 64 ∧
      (kAt lc kt 2 blk2 3).get 2 = some 64 ∧ uAt lc blk2 3 = none ∧
      GenG1.okThen (s0.read lc 20) (fun p => GenG1.okThen (s0.read lc 22) fun q =>
        GenG1.okThen (s0.read lc 23) fun n =>
          isTrue (memEq [p, q, n, .mem GenG13.mem7])) = true ∧
      memeqW m0 = true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 24)) (fun s1 => isTrueR s1.regs[0]?) = true := by
  have hf := g28_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hres⟩, -⟩, hav⟩, hsl⟩, hm2⟩, hb2s⟩, hv24s⟩, hi3⟩, hop⟩, hargs⟩,
    hk0⟩, hk1⟩, hk2⟩, hu⟩, hmeq⟩, hw⟩, hrun⟩ := hf
  refine ⟨hl, ?_, hav, hsl, hm2, ?_, ?_, hi3, hop, hargs, hk0, hk1, hk2, hu, hmeq, hw, hrun⟩
  · revert hres; cases checkG28 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb2s
    simp [blk2, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv24s
    simp [val, hv]

theorem g28Env (hc : checkG28 lc ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG28_spec hl hc
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG28_spec hl hc
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
  memeqs := fun h => by cases h

theorem sep0 : SepFrom GenG13.ι (StkAt E) GenG13.mem7 := by
  intro b al a h ha y hy
  obtain ⟨rfl, rfl⟩ := GenG13.mem7_blocks h
  have ha' : a = GenG13.A := by simp [GenG13.ι, GenG12.ι] at ha; exact ha.symm
  subst ha'
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    have hA : GenG13.A.toNat = 0x20000000000 := rfl
    rw [hsp] at h2
    simp only [hA, Array.size_replicate]
    omega
  · cases hk

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .ptr GenG13.pB) ∨ (r = 1 ∧ x = .ptr pQ) ∨ (r = 2 ∧ x = .int .w64 8) ∨
      x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · split at h
      · rename_i h1; exact Or.inr (Or.inl ⟨h1, h.symm⟩)
      · split at h
        · rename_i h2; exact Or.inr (Or.inr (Or.inl ⟨h2, h.symm⟩))
        · exact Or.inr (Or.inr (Or.inr h.symm))
  · cases h

theorem locMatch0 : LocMatch E s0 2 3 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact ⟨GenG13.A, rfl, by decide⟩
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact ⟨GenG13.A, rfl, by decide⟩
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl rfl
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG13.mem7, rfl, GenG13.memInj7⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl,
    by simp only [MState.word, readMem, m0, GenG13.M7, E, GenG13.A]; decide,
    by simp only [MState.word, readMem, m0, GenG13.M7, E, GenG13.A]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g28Inv0 (h0 : (kAt lc kt 2 blk2 3).get 0 = some 64)
    (h1 : (kAt lc kt 2 blk2 3).get 1 = some 64) (h2 : (kAt lc kt 2 blk2 3).get 2 = some 64) :
    G3Inv E lc (kAt lc kt 2 blk2 3) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG13.mem7, rfl, GenG13.keys7, sep0⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · rw [h1] at hc; cases hc; rfl
    · rw [h2] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v24`, the `LoweredMemEq`: none apply. -/
theorem pre24 {s : LocState} (hop : (val 24).op = .ARM64LoweredMemEq) : G14Pre lc s (val 24) := by
  have hne : ∀ o : Op, o ≠ .ARM64LoweredMemEq → (val 24).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- `Hm` keeps the contract `MemEqOK` at `v24` from `s0` and `m0`: the arguments `runLoc` reads
compare equal (`memEq … = true`), and so do the 8 machine bytes at `A` and at `A + 8`. -/
theorem memEqOK0 (hargs : (val 24).args = #[20, 22, 23, 1])
    (hmeq : GenG1.okThen (s0.read lc 20) (fun p => GenG1.okThen (s0.read lc 22) fun q =>
      GenG1.okThen (s0.read lc 23) fun n =>
        isTrue (memEq [p, q, n, .mem GenG13.mem7])) = true)
    (hw : memeqW m0 = true) : MemEqOK Hm E g L lc s0 (val 24) m0 := by
  intro _ y a0 a1 a2 p q n mm m₁ _ ha0 ha1 ha2 hp hq hn hmm _ _ _ _ hmem hx _ _ _ _ _ _
  rw [hargs] at ha0 ha1 ha2
  simp at ha0 ha1 ha2
  subst ha0 ha1 ha2
  have hmm' : mm = GenG13.mem7 := by
    simp only [s0, Val.mem.injEq] at hmm
    exact hmm.symm
  subst hmm'
  obtain ⟨p0, hp0, hmeq⟩ := GenG1.okThen_spec hmeq
  obtain ⟨q0, hq0, hmeq⟩ := GenG1.okThen_spec hmeq
  obtain ⟨n0, hn0, hmeq⟩ := GenG1.okThen_spec hmeq
  rw [hp0] at hp; cases hp
  rw [hq0] at hq; cases hq
  rw [hn0] at hn; cases hn
  have hw1 : memeqW m₁ = true := by
    rw [← hw]
    unfold memeqW
    rw [hx 0 (by decide), hx 1 (by decide), hx 2 (by decide), hmem]
  refine ⟨_, rfl, rfl, rfl,
    show (if (28 : Reg) = 0 then (if memeqW m₁ then 1 else 0) else m₁.x 28) = m₁.x 28 from
      if_neg (by decide),
    show (if (29 : Reg) = 0 then (if memeqW m₁ then 1 else 0) else m₁.x 29) = m₁.x 29 from
      if_neg (by decide), rfl, ?_⟩
  show ValRel E.ι (memEq [p, q, n, .mem GenG13.mem7]) (if (0 : Reg) = 0 then
    (if memeqW m₁ then 1 else 0) else m₁.x 0)
  rw [isTrue_spec hmeq, hw1]
  rfl

/-- **G28 on `runtime.envKeyEqual`**: from the state before `v24` with `a` at `A` in `R0` (`X0`),
`b` at `A + 8` in `R1` (`X1`), the length 8 in `R2` (`X2`) and `heap 1` 64 bytes 7, under the
runtime `Hm`, `g28_value` runs `CALL runtime.memequal(SB)` (`v24`): `runLoc`'s `R0` holds `true`
and the machine state, related to it before `v24`'s successor under an activation extending `E`
that is again a `G28Env`, has `X0 = 1`. -/
theorem genG28_value_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 24) = .ok s1 ∧ s1.regs[0]? = some (.bool true) ∧
      E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar Hm L ps.toList 0 m0 m1 ∧
      LocMatch E1 s1 2 4 m1 ∧ m1.x 0 = 1 := by
  obtain ⟨hl, hc, hav, hsl, hm2, hb, hv24, hi3, hop, hargs, hk0, hk1, hk2, hu, hmeq, hw, hrun⟩ :=
    facts
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hr1' := isTrueR_spec hr1
  have hE := g28Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64LoweredMemEq → (val 24).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g28_value (H := Hm) (env := GenG2.env)
    hc hE hm2 hb hi3 hv24 (by rw [hop]; rfl) locMatch0 (g28Inv0 hk0 hk1 hk2) (by rw [hu]; trivial)
    (pre24 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun n _ _ _ _ _ _ _ _ _ hn => by
      rw [show icallLead (val 24).op = none by rw [hop]; rfl] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (memEqOK0 hargs hmeq hw) hs1
  have h0 := (hm1'.regs 0 _ hr1').1 0 rfl
  exact ⟨s1, E1, m1, hs1, hr1', hx1, hE1, hp1, hm1', by simpa [ValRel] using h0⟩

end GoFV.Proof.Witness.GenG28
