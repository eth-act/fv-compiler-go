import GoFV.Proof.Gen.G66
import GoFV.Proof.Witness.GenG14
import GoFV.Asm.ConstLoad

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G66 of the genssa validator on `runtime.randn` (a narrow spill)

`std/std/runtime/randn,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`), loaded on P0'
(`p0PrimeSyms`, as `gen-check` runs G56 to G66):

```go
func randn(n uint32) uint32 { return uint32((uint64(uint32(rand())) * uint64(n)) >> 32) }
```

`n` arrives in `R0` (`v6 = ArgIntReg`). Block `b1` (the entry) spills it to its 4-byte spill slot
before the call of `rand` (`v17 = StoreReg v6`, `MOVW R0, n+0(FP)`) and reloads it after
(`v12 = LoadReg v17`, `MOVWU n+0(FP), R1`). G65 spills 64-bit values to 8-byte slots only (`store
shape`, `slot …: frame operand, size or alignment`), so `checkG65` rejects the function; `checkG66`
accepts it with the PC table `tab` and the class table `kt`. The function needs no G48 mode.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g66s_facts`),
`stepLoc` runs `v17` (value 1 of `b1`) from a state `s0` with the `uint32` 7 in `R0` and no slot to
the slot of `n` holding 7. On a framed activation with `G49Env` (the slot at `SP + 24`; not G48's
mode, `outSP = false`), from a machine `m0` holding 7 in `X0`, `g66_value` at the mode `false`
relates that step to the machine, which runs the `MOVW` (`genG66s_witness`): the machine's 4 bytes
at `SP + 24` are 7.
-/

namespace GoFV.Proof.Witness.GenG66s

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/randn,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "randn" 1 1 0
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
type t2 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t1 FUNC 8 8 8 hasptr,direct "func(uint32) uint32" "func(uint32) uint32" 0 1 1
field 0 "n" t2 ? 0
field 1 "" t2 ? 0
aux a2 sym "runtime.randn" "runtime.randn" 1 - 0 - - - - 0
posbase p173 "runtime/rand.go" 1 1 -1
aux a3 name "n" "n" PPARAM t2 0 1 used p173:207:12:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t2 0 1 - p173:207:22:0:0
aux a1 call "AuxCall{runtime.randn}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t4 INT8 1 1 0 comparable,named "int8" "int8"
type t5 INT16 2 2 0 comparable,named "int16" "int16"
type t6 INT32 4 4 0 comparable,named "int32" "int32"
type t7 INT64 8 8 0 comparable,named "int64" "int64"
type t8 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t9 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t10 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t11 INT 8 8 0 comparable,named "int" "int"
type t12 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t13 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t2
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
type t33 RESULTS ? ? ? - "uint64,mem" "" 2 t10,t28
aux a6 sym "runtime.rand" "runtime.rand" 1 - 0 - - - - 0
aux a5 call "AuxCall{runtime.rand}" a6 1 0 1 8 0 0 1
abiparam out 0 t10 - 0 -1
type t34 RESULTS ? ? ? - "uint32,mem" "" 2 t2,t28
slot s1 a3 t2 0 - 0
f b1 t1 a1 18 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t2,UInt64=t10,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t19 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t19 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v7 Const32 t2 0 - p0:0:0:0:0 0 -
v v8 StaticLECall t33 0 a5 p173:209:35:0:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 0 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,32=v15
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t19 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t19 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v7 Const32 t2 0 - p0:0:0:0:0 0 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 0 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,32=v15
freev -
freeb -
cache postorder b1
cache linestarts 173:209:209
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t19 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t19 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v7 Const32 t2 0 - p0:0:0:0:0 0 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 0 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,32=v15
freev -
freeb -
cache postorder b1
cache linestarts 173:209:209
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 0 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 173:209:209
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 0 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 173:209:209
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 0 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 173:209:209
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 0 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 173:209:209
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 173:209:209
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 173:209:209
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 173:209:209
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p173:207:6:2:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticLECall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:0:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 20 "expand calls"
aux a7 nameoff "n+0" a3 0
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 2 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t19 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t19 0 a4 p173:209:2:0:0 0 v5,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,32=v15
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 21 "decompose builtin"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 2 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t19 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t19 0 a4 p173:209:2:0:0 0 v5,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,32=v15
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 2 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t19 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t19 0 a4 p173:209:2:0:0 0 v5,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,32=v15
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 2 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t19 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t19 0 a4 p173:209:2:0:0 0 v5,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,32=v15
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v15 Const64 t14 32 - p0:0:0:0:0 1 -
v v8 StaticCall t33 0 a5 p173:209:35:1:0 2 v1
v v13 ZeroExt32to64 t10 0 - p173:209:49:0:0 1 v6
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v11 Trunc64to32 t2 0 - p173:209:35:0:0 1 v10
v v12 ZeroExt32to64 t10 0 - p173:209:30:0:0 1 v11
v v14 Mul64 t10 0 - p173:209:40:0:0 1 v12,v13
v v16 Rsh64Ux64 t10 1 - p173:209:53:0:0 1 v14,v15
v v17 Trunc64to32 t2 0 - p173:209:53:0:0 1 v16
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v17,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 32=v15
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 33 "lower"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 36 "pair"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 173:209:209
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v6
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v12,v11,v13,v15,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.randn}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
callreg 0:1 - 0 -
aux a5 call "AuxCall{runtime.rand}" a6 1 0 1 8 0 0 1
abiparam out 0 t10 - 0 -1
callreg - 0:1 7fffffff97ffffff -
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v17 StoreReg t2 0 - p173:209:56:1:0 1 v6
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v12 LoadReg t2 0 - p173:209:40:2:0 1 v17
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v12
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v11,v13,v15
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
fstate scheduled,laidout
regalloc 19 v6:R0,v8:[R0],v10:R0,v12:R1,v14:R0,v16:R0,v17:@a3/t2/0/-/0,v18:[]
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v17 StoreReg t2 0 - p173:209:56:1:0 1 v6
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v12 LoadReg t2 0 - p173:209:40:2:0 1 v17
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v12
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v11,v13,v15
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
fstate scheduled,laidout
regalloc 19 v6:R0,v8:[R0],v10:R0,v12:R1,v14:R0,v16:R0,v17:@a3/t2/0/-/0,v18:[]
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 18 1
b b1 Ret p173:209:56:1:0 0 0 - v18 - -
v v6 ArgIntReg t2 0 a7 p173:209:56:1:0 1 -
v v17 StoreReg t2 0 - p173:209:56:1:0 1 v6
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64CALLstatic t33 0 a5 p173:209:35:1:0 2 v1
v v10 SelectN t10 0 - p173:209:35:1:0 1 v8
v v9 SelectN t28 1 - p173:209:35:0:0 1 v8
v v12 LoadReg t2 0 - p173:209:40:2:0 1 v17
v v14 ARM64UMULL t10 0 - p173:209:40:0:0 1 v10,v12
v v16 ARM64SRLconst t10 32 - p173:209:53:0:0 1 v14
v v18 MakeResult t34 0 - p173:209:2:0:0 1 v16,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v11,v13,v15
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 173:209:209
fstate scheduled,laidout
regalloc 19 v6:R0,v8:[R0],v10:R0,v12:R1,v14:R0,v16:R0,v17:@a3/t2/0/-/0,v18:[]
dcllen 3
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t21,t24,t25,t26,t27
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t2,t7,t10,t11,t14,t15,t25,t26,t12,t13,t3,t17,t18,t19,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t34,t33
eof
"#

/-- `std/std/runtime/randn,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "randn" 1
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
type t1 4 4 0 0 - "uint32"
name n1 "n" PPARAM t1 1 "runtime.n" 0 a3
name n2 "~r0" PPARAMOUT t1 1 "runtime.~r0" 0 a4
type t2 8 8 0 0 - "uint64"
name n3 ".autotmp_2" PAUTO t2 3 "runtime..autotmp_2" 0 -
in n1 0 used
in n2 0 outregs
in n3 0 used,autotmp
out n1 0 used
opt n3 0 autotmp
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p173 "runtime/rand.go" 1 1 -1 170 "runtime/rand.go" "runtime/rand.go" 1 1
sym y1 "runtime.randn" 1
curfn p173:207:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 207 281084
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.randn.arginfo1" 0
sym y4 "runtime.randn.argliveinfo" 0
sym y5 "runtime.n" 0
sym y6 "runtime.rand" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p173:207:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p173:207:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p173:207:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p173:207:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p173:207:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p173:207:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p173:209:56:2:0
p 7 7 0 0 0 - MOVW 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/PARAM/0/0/y5/- 0 0 p173:209:56:1:0
p 8 8 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p173:209:56:2:0
p 9 9 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p173:209:35:1:0
p 10 10 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p173:209:35:1:0
p 11 11 0 0 0 - MOVWU 0 MEM/8383/0/0/PARAM/0/0/y5/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p173:209:40:2:0
p 12 12 0 0 0 - UMULL 0 REG/8193/0/0/NONE/0/0/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p173:209:40:2:0
p 13 13 0 0 0 - LSR 0 CONST/0/0/0/NONE/0/32/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p173:209:53:2:0
p 14 14 0 0 0 - RET 0 _ 0 - _ 0 0 p173:209:56:2:0
p 15 15 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 207 281084
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVW MOVWU
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:1:8:50,1:8:-1:-30000:9108
dbgregout n2
dbgpc 1:8:11
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p173:207:6:0:0
p 16 0 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p173:207:6:0:1
p 17 4 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p173:207:6:0:0
p 18 8 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p173:207:6:0:0
p 1 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p173:207:6:0:0
p 2 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p173:207:6:0:0
p 3 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p173:207:6:0:0
p 4 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p173:207:6:0:0
p 5 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p173:207:6:2:0
p 6 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p173:209:56:2:0
p 7 12 0 0 371 - MOVW 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/0/y5/- 0 0 p173:209:56:1:0
p 8 16 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p173:209:56:2:0
p 9 16 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p173:209:35:1:0
p 10 16 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y6/- 0 0 p173:209:35:1:0
p 11 20 0 0 388 - MOVWU 0 MEM/0/0/0/PARAM/48/0/y5/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p173:209:40:2:0
p 12 24 0 0 404 - UMULL 0 REG/8193/0/0/NONE/2/0/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p173:209:40:2:0
p 13 28 0 0 274 - LSR 0 CONST/0/0/0/NONE/17/32/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p173:209:53:2:0
p 14 32 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p173:209:56:2:0
p 19 36 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p173:209:56:2:0
p 20 40 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p173:209:56:2:0
fn y1 8 8 0 0 207 281084
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVW MOVWU
funcaux y2 y2 - - y3 y4 -
text 48 0 fe0f1ff8fd831ff8fd2300d1e01b00b900000094e11b40b9007ca19b00fc60d3fd835ff8fe0741f8c0035fd600000000 1
reloc 16 4 R_CALLARM64 0 y6
pcln y11 y12 y13 y14 y7,y8,y9,y10 y2,y2,_,_,_,y3,y4
usedfiles 170
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0004ff 0
data y4 SDATA 2 1 8000 0000 0
data y7 SRODATA 5 1 28000 0003010900 0
data y8 SRODATA 5 1 28000 0004020800 0
data y9 SRODATA 0 1 28000 - 0
data y10 SRODATA 7 1 28000 00030401030800 0
data y11 SRODATA 7 1 28000 020120091f0200 0
data y12 SRODATA 4 1 28000 d6020c00 0
data y13 SRODATA 6 1 28000 a00303040900 0
data y14 SRODATA 3 1 28000 000c00 0
end
dwarf
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "go:info.runtime.randn$abstract" 0
sym y19 "" 0
sym y20 "go:info.uint32" 0
sym y21 "type:uint32" 0
dwfn y15 y16 y17 y18 y19 "runtime.randn" 170:207 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y18 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "uint32" 0 0 1 p173:207:12:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "uint64" 0 0 1 p173:209:35:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uint32" 0 0 1 p173:207:22:0:0
var 0 0 "n" 5 1 0 0 0 8 y20 "runtime/rand.go" 207 12 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y20 "runtime/rand.go" 207 22 0 1 0 0 -
scope 0 0 - 0,1
dieref y15 3 y18 0
dieoff y18 0:19
data y15 SDWARFFCN 33 0 0 0600000000000030019c2900000000000000002e7e72300001cf01000000000000 6
reloc 0 0 R_USETYPE 0 y21
reloc 1 4 R_DWARFSECREF 0 y18
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y18
reloc 15 4 R_DWARFSECREF 0 y16
reloc 27 4 R_DWARFSECREF 0 y20
data y16 SDWARFLOC 15 0 0 010000040014015004143002910800 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y17 SDWARFRANGE 0 0 0 - 0
data y19 SDWARFLINES 27 0 0 000902000000000000000004ab010a03c9011489065f021c000101 1
reloc 3 8 R_ADDR 0 y1
data y18 SDWARFABSFCN 28 0 1 0572756e74696d652e72616e646e0001cf0101226e00000000000000 1
reloc 23 4 R_DWARFSECREF 0 y20
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`) with P0' (`p0PrimeSyms`, as `gen-check`
runs G56 to G66). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) := do
  let (lc, ps, bs, g) ← GenG2.load fSsa fProg
  let (syms', ps') ← GoFV.Asm.p0PrimeSyms g.syms ps
  return (lc, ps', bs, { g with syms := syms' })

/-- `runLoc`'s context of `randn`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G66's check runs on (`liveCtx`). -/
def lc : LocCtx := liveCtx lc0

/-- P0'. -/
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

/-- The PC table `checkG66` gives. -/
def tab : PcTab := (match checkG66 lc0 ps bs g with
  | .ok (t, _) => t
  | .error _ => [])

/-- The class table `checkG66` gives. -/
def kt : KTab := (match checkG66 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

/-- `b1`, the entry, whose value 1 is `v17 = StoreReg v6`. -/
def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0''s layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame with 8 bytes of extra
space, every symbol at `symA`; `NAME_PARAM` 0 is `SP + 24`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, the home slots at their frame operands and the PC table of `checkG66`; not G48's mode
(`outSP = false`). -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := GenG2.sp0,
    slot := fun k =>
      if k ∈ homeSlots lc then (g.slotOp k).map (fun p => frameOff L p.1 p.2) else none,
    g := 0x9000, lr := 0, fp := 0, framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- A state before `v17`: the `uint32` 7 in `R0` (Go register 0, `v6`'s home), every other register
`poison`, no slot, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 9 none, args := [], mem0 := GenG2.mem0, images := #[] },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w32 7 else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v17`: the activation's `g` and `FP`, the PC of `v17`, 7 in `X0`, the
memory 0. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else
      if k = 0 then 7 else 0,
    sp := GenG2.sp0, v := fun _ => 0,
    nzcv := ⟨false, false, false, false⟩, pc := E.pcOf 1 1, mem := fun _ => 0 }

/-- The home slots lie above the saved `LR` and below `2^64`. -/
def slotsFit : Bool :=
  (homeSlots lc).all fun k =>
    match g.slotOp k with
    | some (nc, off) => decide (8 ≤ frameOff L nc off) &&
        decide (GenG2.sp0.toNat + (frameOff L nc off).toNat + 8 ≤ 2 ^ 64)
    | none => true

/-- A home `h` that is a slot at `SP + 24` (`slot`) of 4 bytes (`size`). Generic in its inputs, so
that its spec never makes the kernel evaluate the function. -/
def slotAt (h : Option Location) (slot : SlotKey → Option Int) (size : SlotKey → Nat) : Bool :=
  match h with
  | some (.slot k) => slot k == some 24 && size k == 4
  | _ => false

theorem slotAt_spec {h : Option Location} {slot : SlotKey → Option Int} {size : SlotKey → Nat}
    (H : slotAt h slot size = true) : ∃ k, h = some (.slot k) ∧ slot k = some 24 ∧ size k = 4 := by
  unfold slotAt at H
  split at H
  · rename_i k
    simp only [Bool.and_eq_true, beq_iff_eq] at H
    exact ⟨k, rfl, H.1, H.2⟩
  · cases H

/-- After `v17`: the slot of `n` (home `h`) holds the `uint32` 7. -/
def holds7 (h : Option Location) (s : LocState) : Bool :=
  match h with
  | some (.slot k) =>
    match s.slots.lookup k with
    | some (.int .w32 n) => n == 7
    | _ => false
  | _ => false

theorem holds7_spec {h : Option Location} {s : LocState} (H : holds7 h s = true) :
    ∃ k, h = some (.slot k) ∧ s.slots.lookup k = some (.int .w32 7) := by
  unfold holds7 at H
  split at H
  · rename_i k
    split at H
    · rename_i n hn
      simp only [beq_iff_eq] at H
      subst H
      exact ⟨k, rfl, hn⟩
    · cases H
  · cases H

/-- What compiled evaluation checks on `randn`: it holds an arm64 op; on P0', `checkG66` accepts it
with `tab` and `kt` and `checkG65` does not; it accesses no frame variable, its home slots fit and
it needs no G48 mode; G2's symbols have no float constant; `b1` holds `v17` (`StoreReg v6`) at
index 1, where G35's table is empty and the class table gives `R0` class 32; `v17`'s home is a
slot at `SP + 24` of 4 bytes; `stepLoc` runs `v17` from `s0` to that slot holding 7. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG66 lc0 ps bs g).toOption == some (tab, kt) && (checkG65 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && slotsFit && needs48 lc == false &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 17).isSome && blk.values[1]? == some 17 &&
    (val 17).op == .StoreReg && (val 17).id == 17 &&
    (constRo (symNames g)).isEmpty &&
    uL35 lc (uIn35 lc 1) blk 1 == [] && (kAt lc kt 1 blk 1).get 0 == some 32 &&
    slotAt (lc.home 17) E.slot (fun k => (E.lc.slotTy k).size) &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 17)) (holds7 (lc.home 17))

theorem g66s_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG66 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG65 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ slotsFit = true ∧ needs48 lc = false ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 17 = some (val 17) ∧ blk.values[1]? = some 17 ∧
      (val 17).op = .StoreReg ∧ (val 17).id = 17 ∧
      (constRo (symNames g)).isEmpty = true ∧
      uL35 lc (uIn35 lc 1) blk 1 = [] ∧ (kAt lc kt 1 blk 1).get 0 = some 32 ∧
      slotAt (lc.home 17) E.slot (fun k => (E.lc.slotTy k).size) = true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 17)) (holds7 (lc.home 17)) = true := by
  have hf := g66s_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h65, hav, hfit, h48, hm1, hbs, hvs, hi1, hop, hid, hro, hu1, hk0, hat,
    hrun⟩ := hf
  refine ⟨hl, ?_, h65, hav, hfit, h48, hm1, ?_, ?_, hi1, hop, hid, hro, hu1, hk0, hat, hrun⟩
  · revert hres; cases checkG66 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g66Env (hc : checkG66 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
    (hav : (accessedVars lc).isEmpty = true) (hfit : slotsFit = true) :
    G49Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
            link := rfl
            pcOf := rfl
            retOut := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -, -, -⟩ :=
                checkG66L_spec hl (checkG66_spec hc).2
              intro p hp
              exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := GenG2.addrAgree
            glob := fun _ _ _ _ => rfl
            syms := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -, -, -⟩ :=
                checkG66L_spec hl (checkG66_spec hc).2
              intro y
              have hs : L.sym y = GenG2.symA := rfl
              rw [hs]
              refine ⟨by decide, fun p hp => ?_⟩
              exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
            calls := fun h => by cases h
            slot := fun k hk nc off hs => by simp [E, hk, hs]
            extra := by show 0 ≤ (8 : Int); decide
            frame := by
              refine ⟨by show 4096 + 8 ≤ GenG2.sp0.toNat; decide,
                by show GenG2.sp0.toNat + 8 ≤ 2 ^ 64; decide, fun k off hk => ?_⟩
              simp only [E] at hk
              split at hk
              · rename_i hmem
                obtain ⟨⟨nc, o⟩, hso, rfl⟩ := Option.map_eq_some_iff.1 hk
                have := List.all_eq_true.1 hfit k hmem
                simp only [hso, Bool.and_eq_true, decide_eq_true_eq] at this
                exact this
              · cases hk }
          vars := by
            intro x hx
            simp [List.isEmpty_iff.1 hav] at hx }
        wbs := fun h => by cases h }
      icalls := fun h => by cases h }
    memeqs := fun h => by cases h }
  vars := by
    intro x hx
    simp [List.isEmpty_iff.1 hav] at hx

/-! ## The state -/

/-- G2's symbols have no float constant: `RoPre56` holds at `s0`. -/
theorem ro0 (hro : (constRo (symNames g)).isEmpty = true) : RoPre56 g s0 := by
  intro mm _
  rw [List.isEmpty_iff.1 hro]
  intro n a h
  cases h

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w32 7) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0
      exact .inl ⟨h0, h.symm⟩
    · exact .inr h.symm
  · cases h

/-- `R0` is Go register 0, the obj register `X0`. -/
theorem objX0 : objX? 0 = some (BitVec.ofNat 5 0) := by decide

theorem objV0 : objV? 0 = none := by decide

theorem locMatch0 : LocMatch E s0 1 1 m0 where
  regs := by
    intro r x hx
    rcases s0_regs hx with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rw [objX0] at hk
        cases hk
        show ((m0.x (BitVec.ofNat 5 0)).setWidth 32 : BitVec 32) = 7
        decide
      · rw [objV0] at hk
        cases hk
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl,
    by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g66Inv0 (hk0 : (kAt lc kt 1 blk 1).get 0 = some 32) :
    G3Inv E lc (kAt lc kt 1 blk 1) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, GenG2.keys0, GenG2.sep0⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [hk0] at hc
      cases hc
      show kNarrow 32 32 = true
      decide
    · trivial
  slots := by intro k v h; simp [s0] at h

/-! ## `v17`: `StoreReg v6` (`MOVW R0, n+0(FP)`) -/

/-- The per-value premises of G54 on `v17`, `StoreReg`: none of them applies. -/
theorem pre54 (hop : (val 17).op = .StoreReg) : G54Pre lc s0 (val 17) := by
  have hne : ∀ o : Op, o ≠ .StoreReg → (val 17).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩,
    ?_, ?_⟩, ?_⟩, fun h => absurd h (hne _ (by decide)), fun h => absurd h (hne _ (by decide))⟩
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

/-- **G66 on `runtime.randn`** (`v17 = StoreReg v6`, the narrow spill `MOVW R0, n+0(FP)`):
`checkG65` rejects the function and `checkG66` accepts it. From a state with the `uint32` 7 in
`R0`, `stepLoc` runs `v17` to the slot of `n` holding 7, and `g66_value` (at the mode `false`, the
function needing no G48 mode) relates it to a machine run from `m0`, which holds 7 in `X0`, to a
state whose 4 bytes at `SP + 24`, the slot, are 7, under an activation extending `E` that is again
a `G49Env`. -/
theorem genG66s_witness :
    (checkG65 lc0 ps bs g).toOption = none ∧
      ∃ s1 E1 m1 k, stepLoc GenG2.env lc s0 (val 17) = .ok s1 ∧ lc.home 17 = some (.slot k) ∧
        s1.slots.lookup k = some (.int .w32 7) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 2 m1 ∧
        ((readMem m1.mem (GenG2.sp0 + BitVec.ofInt 64 24) 4).setWidth 64).setWidth 32 = 7 := by
  obtain ⟨hl, hc, h65, hav, hfit, h48, hm1, hb, hv17, hi1, hop, hid, hro, hu1, hk0, hat, hrun⟩ :=
    facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  obtain ⟨k, hk, hlook⟩ := holds7_spec hr
  have hE := g66Env hc hl hav hfit
  have hne : ∀ o : Op, o ≠ .StoreReg → (val 17).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  -- `g66_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 17 = some (val 17) := by
    rw [← liveCtx_ctx (lc := lc0)]; exact hv17
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -, -⟩ := g66_value (H := GenG2.H0) (env := GenG2.env)
    (osp := false) hc hE hl0 hm0 hb0 hi1 hv0 (by rw [hop]; rfl) locMatch0 (g66Inv0 hk0)
    (fun h => by cases h) (fun h => by cases h)
    (fun h => by
      have h' : needs48 lc = true := h
      rw [h48] at h'
      cases h')
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 1); rw [hu1]; intro e he; cases he)
    (pre54 hop) (ro0 hro)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => by cases h) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide)))
    ⟨fun h => absurd h (hne _ (by decide)), fun h => absurd h (hne _ (by decide))⟩ hs1
  refine ⟨h65, s1, E1, m1, k, hs1, hk, hlook, hx1, hE1, hp1, hm1', ?_⟩
  obtain ⟨o, ho, hrel⟩ := hm1'.slots k _ hlook
  obtain ⟨hEq, -⟩ := hx1
  have hslot : E1.slot = E.slot := by rw [hEq]
  have hsp : E1.sp = E.sp := by rw [hEq]
  have hlc : E1.lc = E.lc := by rw [hEq]
  obtain ⟨k', hh', h24, h4⟩ := slotAt_spec hat
  rw [hk] at hh'
  cases hh'
  rw [hslot, h24] at ho
  cases ho
  unfold SlotRel at hrel
  rw [hlc, h4, hsp] at hrel
  simp only [ValRel] at hrel
  exact hrel

end GoFV.Proof.Witness.GenG66s
