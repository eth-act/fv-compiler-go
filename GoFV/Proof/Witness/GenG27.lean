import GoFV.Proof.Gen.G27
import GoFV.Proof.Witness.GenG26

/-!
# Non-vacuity witness: slice G27 of the genssa validator on `regexp.newLazyFlag`

`std/std/regexp/newLazyFlag,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`):

```go
func newLazyFlag(r1, r2 rune) lazyFlag {
	return lazyFlag(uint64(r1)<<32 | uint64(uint32(r2)))
}
```

`checkG26` rejects it (`v15: op ORshiftLL`); `checkG27` accepts it with the PC table `tab` and the
class table `kt`. Block `b1`: `v10 = MOVWreg v7` (`MOVW R0, R2`), `v14 = MOVWUreg v8`
(`MOVWU R1, R1`), `v15 = ORshiftLL [32] v14 v10` (`ORR R2<<32, R1, R0`), `MakeResult`, then the
`RET`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g27_facts`),
`stepLoc` runs `v15` from a state with `uint32(r2) = 2` in `R1` and `r1 = 1` in `R2`: `R0` then
holds `2 | 1 << 32 = 0x100000002`. On a framed activation with `G10Env` (as `GenG25`'s) with
`X1 = 2` and `X2 = 1`, `g27_value` runs the `ORR`: the machine's `X0` is `0x100000002`
(`genG27_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG27

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/regexp/newLazyFlag,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "regexp"
func "newLazyFlag" 1 0 0
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
type t2 INT32 4 4 0 comparable,named "rune" "int32"
type t3 UINT64 8 8 0 comparable,named "lazyFlag" "regexp.lazyFlag"
type t1 FUNC 8 8 8 hasptr,direct "func(rune, rune) lazyFlag" "func(int32, int32) regexp.lazyFlag" 0 2 1
field 0 "r1" t2 ? 0
field 1 "r2" t2 ? 0
field 2 "" t3 ? 0
aux a2 sym "regexp.newLazyFlag" "regexp.newLazyFlag" 1 - 0 - - - - 0
posbase p5 "regexp/exec.go" 1 1 -1
aux a3 name "r1" "r1" PPARAM t2 0 1 used p5:124:18:0:0
aux a4 name "r2" "r2" PPARAM t2 4 1 used p5:124:22:0:0
aux a5 name "~r0" "~r0" PPARAMOUT t3 0 1 - p5:124:31:0:0
aux a1 call "AuxCall{regexp.newLazyFlag}" a2 1 2 1 8 8 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t2 a4 1 4
abiparam out 0 t3 a5 0 -1
type t4 BOOL 1 1 0 comparable,named "bool" "bool"
type t5 INT8 1 1 0 comparable,named "int8" "int8"
type t6 INT16 2 2 0 comparable,named "int16" "int16"
type t7 INT32 4 4 0 comparable,named "int32" "int32"
type t8 INT64 8 8 0 comparable,named "int64" "int64"
type t9 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t10 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t11 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t12 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t13 INT 8 8 0 comparable,named "int" "int"
type t14 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t15 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t16 UINT 8 8 0 comparable,named "uint" "uint"
type t17 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t18 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t9
type t20 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t7
type t21 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t11
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
type t35 PTR 8 8 8 hasptr,direct,comparable "*rune" "*int32" t2
type t36 PTR 8 8 8 hasptr,direct,comparable "*lazyFlag" "*regexp.lazyFlag" t3
type t37 RESULTS ? ? ? - "lazyFlag,mem" "" 2 t3,t30
slot s1 a3 t2 0 - 0
slot s2 a4 t2 0 - 0
f b1 t1 a1 17 1
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t8,UInt8=t9,UInt16=t10,UInt32=t11,UInt64=t12,Int=t13,Float32=t14,Float64=t15,UInt=t16,Uintptr=t17,String=t18,BytePtr=t19,Int32Ptr=t20,UInt32Ptr=t21,IntPtr=t22,UintptrPtr=t23,Float32Ptr=t24,Float64Ptr=t25,BytePtrPtr=t26,Complex64=t27,Complex128=t28,UnsafePtr=t29,Mem=t30,Flags=t31,Void=t32,Int128=t33,ResultMem=t34
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 3 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t35 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t36 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v9 Const64 t3 0 - p0:0:0:0:0 0 -
v v10 SignExt32to64 t12 0 - p5:125:25:0:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 0 - p5:125:28:0:0 1 v10,v11
v v13 Copy t11 0 - p5:125:49:2:0 1 v8
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v13
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v16 Copy t3 0 - p5:125:33:2:0 1 v15
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v16,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9,32=v11
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 3 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t35 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t36 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v9 Const64 t3 0 - p0:0:0:0:0 0 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 0 - p5:125:28:0:0 1 v10,v11
v v13 Copy t11 0 - p5:125:49:2:0 1 v8
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v13
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v16 Copy t3 0 - p5:125:33:2:0 1 v15
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v16,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9,32=v11
freev -
freeb -
cache postorder b1
cache linestarts 5:125:125
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 3 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t35 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t36 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 2 -
v v9 Const64 t3 0 - p0:0:0:0:0 0 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 0 - p5:125:28:0:0 1 v10,v11
v v13 Copy t11 0 - p5:125:49:2:0 0 v8
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v15 Or64 t12 0 - p5:125:33:0:0 2 v12,v14
v v16 Copy t3 0 - p5:125:33:2:0 0 v15
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9,32=v11
freev -
freeb -
cache postorder b1
cache linestarts 5:125:125
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 0 - p5:125:28:0:0 1 v10,v11
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:125:125
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 0 - p5:125:28:0:0 1 v10,v11
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:125:125
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 0 - p5:125:28:0:0 1 v10,v11
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:125:125
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 0 - p5:125:28:0:0 1 v10,v11
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:125:125
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:125:125
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:125:125
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:125:125
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p5:124:6:2:0 1 -
v v8 Arg t2 0 a4 p5:124:6:2:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v16,v13,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 20 "expand calls"
aux a6 nameoff "r1+0" a3 0
aux a7 nameoff "r2+0" a4 0
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
v v16 SB t17 0 - p0:0:0:0:0 0 -
v v13 SP t17 0 - p0:0:0:0:0 2 -
v v9 OffPtr t35 0 - p0:0:0:0:0 0 v13
v v6 LocalAddr t36 0 a5 p5:125:2:0:0 0 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9,32=v11
freev v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 21 "decompose builtin"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
v v16 SB t17 0 - p0:0:0:0:0 0 -
v v13 SP t17 0 - p0:0:0:0:0 2 -
v v9 OffPtr t35 0 - p0:0:0:0:0 0 v13
v v6 LocalAddr t36 0 a5 p5:125:2:0:0 0 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9,32=v11
freev v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
v v16 SB t17 0 - p0:0:0:0:0 0 -
v v13 SP t17 0 - p0:0:0:0:0 2 -
v v9 OffPtr t35 0 - p0:0:0:0:0 0 v13
v v6 LocalAddr t36 0 a5 p5:125:2:0:0 0 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9,32=v11
freev v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
v v16 SB t17 0 - p0:0:0:0:0 0 -
v v13 SP t17 0 - p0:0:0:0:0 2 -
v v9 OffPtr t35 0 - p0:0:0:0:0 0 v13
v v6 LocalAddr t36 0 a5 p5:125:2:0:0 0 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9,32=v11
freev v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v11 Const64 t16 32 - p0:0:0:0:0 1 -
v v10 SignExt32to64 t12 0 - p5:125:25:1:0 1 v7
v v14 ZeroExt32to64 t12 0 - p5:125:48:0:0 1 v8
v v12 Lsh64x64 t12 1 - p5:125:28:0:0 1 v10,v11
v v15 Or64 t12 0 - p5:125:33:0:0 1 v12,v14
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 32=v11
freev v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 33 "lower"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 36 "pair"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 5:125:125
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v12,v11,v6,v9,v13,v16,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a1 call "AuxCall{regexp.newLazyFlag}" a2 1 2 1 8 8 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t2 a4 1 4
abiparam out 0 t3 a5 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v2,v3,v4,v5,v6,v9,v11,v12,v13,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
fstate scheduled,laidout
regalloc 18 v7:R0,v8:R1,v10:R2,v14:R1,v15:R0,v17:[]
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v2,v3,v4,v5,v6,v9,v11,v12,v13,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
fstate scheduled,laidout
regalloc 18 v7:R0,v8:R1,v10:R2,v14:R1,v15:R0,v17:[]
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 17 1
b b1 Ret p5:125:49:1:0 0 0 - v17 - -
v v7 ArgIntReg t2 0 a6 p5:125:49:1:0 1 -
v v8 ArgIntReg t2 1 a7 p5:125:49:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWreg t12 0 - p5:125:25:1:0 1 v7
v v14 ARM64MOVWUreg t12 0 - p5:125:48:0:0 1 v8
v v15 ARM64ORshiftLL t12 32 - p5:125:33:0:0 1 v14,v10
v v17 MakeResult t37 0 - p5:125:2:0:0 1 v15,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v2,v3,v4,v5,v6,v9,v11,v12,v13,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 5:125:125
fstate scheduled,laidout
regalloc 18 v7:R0,v8:R1,v10:R2,v14:R1,v15:R0,v17:[]
dcllen 3
end
frontend
end
ptrcache t3,t6,t7,t8,t9,t11,t12,t13,t14,t15,t17,t18,t19,t23,t26,t29
typelink t2=t7,t20=t35,t30=t34
typeorder t5,t9,t6,t10,t2=t7,t11,t8,t12,t3,t13,t16,t17,t27,t28,t14,t15,t4,t19,t20=t35,t21,t36,t22,t23,t24,t25,t26,t1,t18,t29,t30,t32,t31,t33,t34,t37
eof
"#

/-- `std/std/regexp/newLazyFlag,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "regexp"
func "newLazyFlag" 1
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
type t1 4 4 0 0 - "rune"
name n1 "r1" PPARAM t1 1 "regexp.r1" 0 a3
name n2 "r2" PPARAM t1 1 "regexp.r2" 0 a4
type t2 8 8 0 0 - "lazyFlag"
name n3 "~r0" PPARAMOUT t2 1 "regexp.~r0" 0 a5
in n1 0 used
in n2 4 used
in n3 0 outregs
out n1 0 used
out n2 4 used
opt n3 0 outregs
stack 0 0 8
end
genin
posbase p5 "regexp/exec.go" 1 1 -1 4 "regexp/exec.go" "regexp/exec.go" 1 1
sym y1 "regexp.newLazyFlag" 1
curfn p5:124:6:0:0 0 0
regargs 8192:0:t1,8193:4:t1
text y1 0 0 0 0 124 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "regexp.newLazyFlag.arginfo1" 0
sym y4 "regexp.newLazyFlag.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p5:124:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p5:124:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p5:124:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p5:124:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p5:124:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p5:124:6:2:0
p 6 6 0 0 0 - MOVW 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p5:125:25:1:0
p 7 7 0 0 0 - MOVWU 0 REG/8193/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p5:125:48:2:0
p 8 8 0 0 0 - ORR 0 SHIFT/0/0/0/NONE/0/163840/-/- 8193 - REG/8192/0/0/NONE/0/0/-/- 0 0 p5:125:33:2:0
p 9 9 0 0 0 - RET 0 _ 0 - _ 0 0 p5:125:49:2:0
p 10 10 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 124 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STPW LDPW
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgslot 1 n2 t1 0
dbgvar 0 n1 0
dbgvar 1 n2 1
dbgloc 0 1:-10000:1:15:50
dbgloc 1 1:-10000:1:14:51
dbgregout n3
dbgpc 1:15:9,1:14:8
end
asm
sym y5 "" 0
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p5:124:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p5:124:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p5:124:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p5:124:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p5:124:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p5:124:6:2:0
p 6 0 0 0 369 - MOVW 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p5:125:25:1:0
p 7 4 0 0 369 - MOVWU 0 REG/8193/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p5:125:48:2:0
p 8 8 0 0 51 - ORR 0 SHIFT/0/0/0/NONE/8/163840/-/- 8193 - REG/8192/0/0/NONE/2/0/-/- 0 0 p5:125:33:2:0
p 9 12 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p5:125:49:2:0
fn y1 8 0 0 0 124 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STPW LDPW
funcaux y2 y2 - - y3 y4 -
text 16 0 027c4093e103012a208002aac0035fd6 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 4
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 5 1 8000 00040404ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 0 1 28000 - 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040400 0
data y9 SRODATA 3 1 28000 020400 0
data y10 SRODATA 3 1 28000 0a0400 0
data y11 SRODATA 4 1 28000 fc010400 0
data y12 SRODATA 3 1 28000 000400 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "go:info.regexp.newLazyFlag$abstract" 0
sym y17 "" 0
sym y18 "go:info.int32" 0
sym y19 "go:info.regexp.lazyFlag" 0
sym y20 "type:regexp.lazyFlag" 0
dwfn y13 y14 y15 y16 y17 "regexp.newLazyFlag" 4:124 1 0 1 275
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2,n3
dwprecursor y1 y16 n1,n2,n3
dwname n1 1 1 0 0 0 0 0 0 - - "int32" 0 0 1 p5:124:18:0:0
dwname n2 1 1 0 0 0 0 4 0 - - "int32" 0 0 1 p5:124:22:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "regexp.lazyFlag" 0 0 1 p5:124:31:0:0
var 0 0 "r1" 5 1 0 0 0 8 y18 "regexp/exec.go" 124 18 0 0 1 0 v0
var 1 0 "r2" 5 1 0 0 0 12 y18 "regexp/exec.go" 124 22 0 1 1 0 v1
var 2 0 "~r0" 5 1 1 0 0 0 y19 "regexp/exec.go" 124 31 0 2 0 0 -
scope 0 0 - 0,1,2
dieref y13 3 y16 0
dieref y13 5 y16 1
dieoff y16 0:23,1:32
data y13 SDWARFFCN 41 0 0 0600000000000010019c2900000000000000002900000000000000002e7e723000017c000000000000 8
reloc 0 0 R_USETYPE 0 y20
reloc 1 4 R_DWARFSECREF 0 y16
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y16
reloc 15 4 R_DWARFSECREF 0 y14
reloc 20 4 R_DWARFSECREF 0 y16
reloc 24 4 R_DWARFSECREF 9 y14
reloc 35 4 R_DWARFSECREF 0 y19
data y14 SDWARFLOC 18 0 0 01000004000c015000010000040008015100 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 24 0 0 0009020000000000000000040503f700140637020c000101 1
reloc 3 8 R_ADDR 0 y1
data y16 SDWARFABSFCN 42 0 1 057265676578702e6e65774c617a79466c616700017c0122723100000000000022723200000000000000 2
reloc 28 4 R_DWARFSECREF 0 y18
reloc 37 4 R_DWARFSECREF 0 y18
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

/-- The PC table `checkG27` gives (`b1`: one entry per value `v7`, `v8`, `v1`, `v10`, `v14`,
`v15`, `v17`, then the `RET`). -/
def tab : PcTab := [(1, [5, 5, 5, 5, 7, 8, 9, 9])]

/-- The class table `checkG27` gives (nothing known at the entry). -/
def kt : KTab := (match checkG27 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG27`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The empty memory. -/
def mem0 : Mem := {}

/-- The `runLoc` state before `v15`: `uint32(r2) = 2` in `R1`, `r1 = 1` in `R2`, every other
register `poison`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 1 then .int .w64 2 else if i.val = 2 then .int .w64 1 else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v15`: `X1 = 2`, `X2 = 1`, the activation's `g` and `FP`, the PC of `v15`,
a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 1 then 2 else if k = 2 then 1 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 5, mem := fun _ => 0 }

/-- The register holds the 64-bit integer `0x100000002`. -/
def isRes : Option Val → Bool
  | some (.int .w64 x) => x == 0x100000002
  | _ => false

theorem isRes_spec {o : Option Val} (h : isRes o = true) : o = some (.int .w64 0x100000002) := by
  unfold isRes at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on the function: it holds an arm64 op, `checkG27` accepts it
with `tab` and `kt` and `checkG26` does not; it accesses no frame variable and has no home slot;
`b1` holds `v15` (`ORshiftLL`) at index 5, `R1` and `R2` have class 64 before `v15` and nothing
is in the upper-bit table there; `stepLoc` runs `v15` from `s0` to `R0 = 0x100000002`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG27 lc ps bs g).toOption == some (tab, kt) && (checkG26 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 15).isSome && blk1.values[5]? == some 15 && (val 15).op == .ARM64ORshiftLL &&
    (kAt lc kt 1 blk1 5).get 1 == some 64 && (kAt lc kt 1 blk1 5).get 2 == some 64 &&
    uAt lc blk1 5 == none &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 15)) fun s1 => isRes s1.regs[0]?

theorem g27_facts : gFacts = true := by
  native_decide

/-- The facts of `g27_facts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG27 lc ps bs g = .ok (tab, kt) ∧
      (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 1 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 1 = some blk1 ∧ lc.ctx.f.value? 15 = some (val 15) ∧
      blk1.values[5]? = some 15 ∧ (val 15).op = .ARM64ORshiftLL ∧
      (kAt lc kt 1 blk1 5).get 1 = some 64 ∧ (kAt lc kt 1 blk1 5).get 2 = some 64 ∧
      uAt lc blk1 5 = none ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 15)) (fun s1 => isRes s1.regs[0]?) = true := by
  have hf := g27_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hres⟩, -⟩, hav⟩, hsl⟩, hm1⟩, hb1s⟩, hv15s⟩, hi5⟩, hop⟩, hk1⟩, hk2⟩,
    hu⟩, hrun⟩ := hf
  refine ⟨hl, ?_, hav, hsl, hm1, ?_, ?_, hi5, hop, hk1, hk2, hu, hrun⟩
  · revert hres; cases checkG27 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [blk1, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv15s
    simp [val, hv]

theorem g27Env (hc : checkG27 lc ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
    (hav : (accessedVars lc).isEmpty = true) (hsl : (homeSlots lc).isEmpty = true) :
    G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG27_spec hl hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := GenG12.addrAgree
        glob := fun _ _ _ _ => rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG27_spec hl hc
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

theorem memInj0 (mm : Memory) : MemInj GenG12.ι mem0 mm where
  nil := rfl
  mapped := by intro b al h; simp [mem0] at h
  inj := by intro b al b' al' a a' h; simp [mem0] at h
  bytes := ⟨fun _ _ => False, by intro b al a h; simp [mem0] at h⟩

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 1 ∧ x = .int .w64 2) ∨ (r = 2 ∧ x = .int .w64 1) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · split at h
      · rename_i h2; exact Or.inr (Or.inl ⟨h2, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatch0 : LocMatch E s0 1 5 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl rfl
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g27Inv0 (h1 : (kAt lc kt 1 blk1 5).get 1 = some 64)
    (h2 : (kAt lc kt 1 blk1 5).get 2 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk1 5) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h1] at hc; cases hc; rfl
    · rw [h2] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v15`, the `ORshiftLL`: none apply. -/
theorem pre15 {s : LocState} (hop : (val 15).op = .ARM64ORshiftLL) : G14Pre lc s (val 15) := by
  have hne : ∀ o : Op, o ≠ .ARM64ORshiftLL → (val 15).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G27 on `regexp.newLazyFlag`**: from the state before `v15` with `uint32(r2) = 2` in `R1`
(`X1 = 2`) and `r1 = 1` in `R2` (`X2 = 1`), `g27_value` runs `ORR R2<<32, R1, R0` (`v15`):
`runLoc`'s `R0` holds `0x100000002` and the machine state, related to it before `v17` under an
activation extending `E`, has `X0 = 0x100000002`. -/
theorem genG27_value_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 15) = .ok s1 ∧
      s1.regs[0]? = some (.int .w64 0x100000002) ∧
      E.Extends E1 ∧ G10Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E1 s1 1 6 m1 ∧ m1.x 0 = 0x100000002 := by
  obtain ⟨hl, hc, hav, hsl, hm1, hb, hv15, hi5, hop, hk1, hk2, hu, hrun⟩ := facts
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hr1' := isRes_spec hr1
  have hE := g27Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64ORshiftLL → (val 15).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g27_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm1 hb hi5 hv15 (by rw [hop]; rfl) locMatch0 (g27Inv0 hk1 hk2) (by rw [hu]; trivial)
    (pre15 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  exact ⟨s1, E1, m1, hs1, hr1', hx1, hE1, hp1, hm1',
    valRel_i64 hA ((hm1'.regs 0 _ hr1').1 0 rfl)⟩

end GoFV.Proof.Witness.GenG27
