import GoFV.Proof.Gen.G66
import GoFV.Proof.Witness.GenG14
import GoFV.Asm.ConstLoad

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G66b on `u32rand` of `test/ken_divconst` (an elided extension)

`test/ken_divconst/main/u32rand,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`), loaded on P0'
(`p0PrimeSyms`, as `gen-check` runs G56 to G66):

```go
func u32rand() uint32 {
	a := uint32(rand.Uint32())
	a >>= uint(rand.Intn(32))
	return a
}
```

Block `b1` (the only one) spills the `uint32` result of `rand.Uint32` to its 4-byte slot
(`v2 = StoreReg v8`, `MOVW R0, a-4(SP)`), reloads it after the call of `rand.Intn`
(`v16 = LoadReg v2`, `MOVWU a-4(SP), R1`, zero-extending: `uint32` is unsigned) and zero-extends it
for the shift (`v4 = MOVWUreg v16`, both in `R1`). Genssa emits no code for `v4`: the reload already
extended (`ssa.go:1353-1383`); every slice before G66b expects `MOVWU R1, R1` there, so `checkG65`
rejects the function, and `checkG66` accepts it with the PC table `tab` and the class table `kt`.
The function needs no G48 mode.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g66b_facts`):
`v4` is value 10 of `b1`, an extension genssa elides (`elide66b`: 32 bits, unsigned), before which
G35's table holds the reload's entry `(R1, 32, unsigned)` (`reloadEntry35`) and only it; `stepLoc`
runs `v4` from a state `s0` with the `uint32` `0xDEADBEEF` in `R1` to `R1` holding the `uint64`
`0xDEADBEEF`. On a framed activation with `G49Env` (the slot at `SP + 12`; not G48's mode,
`outSP = false`), from a machine `m0` holding `0xDEADBEEF` in `X1` (the zero extension of its low
32 bits, as the table says), `g66_value` at the mode `false` relates that step to the machine
(`genG66b_witness`): `X1` is related to the `uint64` `0xDEADBEEF`.
-/

namespace GoFV.Proof.Witness.GenG66b

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/ken_divconst/main/u32rand,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "u32rand" 1 0 0
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
type t2 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t1 FUNC 8 8 8 hasptr,direct "func() uint32" "func() uint32" 0 0 1
field 0 "" t2 ? 0
aux a2 sym "main.u32rand" "main.u32rand" 1 - 0 - - - - 0
posbase p2 "./divconst.go" 1 1 -1
aux a3 name "~r0" "~r0" PPARAMOUT t2 0 1 - p2:266:16:0:0
aux a1 call "AuxCall{main.u32rand}" a2 1 0 1 8 0 0 1
abiparam out 0 t2 a3 0 -1
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
type t33 RESULTS ? ? ? - "uint32,mem" "" 2 t2,t28
aux a5 sym "math/rand.Uint32" "math/rand.Uint32" 1 - 0 - - - - 0
aux a4 call "AuxCall{math/rand.Uint32}" a5 1 0 1 8 0 0 1
abiparam out 0 t2 - 0 -1
type t34 RESULTS ? ? ? - "int,mem" "" 2 t11,t28
aux a7 sym "math/rand.Intn" "math/rand.Intn" 1 - 0 - - - - 0
aux a6 call "AuxCall{math/rand.Intn}" a7 1 1 1 8 8 1 1
abiparam in 0 t11 - 0 0
abiparam out 0 t11 - 0 -1
aux a8 name "a" "a" PAUTO t2 0 1 used p2:267:2:0:0
slot s1 a8 t2 0 - 0
f b1 t1 a1 15 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t2,UInt64=t10,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t19 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const32 t2 0 - p0:0:0:0:0 0 -
v v6 StaticLECall t33 0 a4 p2:267:25:0:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:0:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v13 Copy t14 0 - p2:268:22:2:0 1 v12
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v13
v v15 MakeResult t33 0 - p2:269:2:0:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 0=v5,32=v9
freev -
freeb -
dcllen 4
end
pass 1 "number lines"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t19 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const32 t2 0 - p0:0:0:0:0 0 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v13 Copy t14 0 - p2:268:22:2:0 1 v12
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v13
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 0=v5,32=v9
freev -
freeb -
cache postorder b1
cache linestarts 2:267:269
dcllen 4
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t19 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const32 t2 0 - p0:0:0:0:0 0 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 2 v10
v v13 Copy t14 0 - p2:268:22:2:0 0 v12
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 0=v5,32=v9
freev -
freeb -
cache postorder b1
cache linestarts 2:267:269
dcllen 4
end
pass 3 "early deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:267:269
dcllen 4
end
pass 4 "short circuit"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:267:269
dcllen 4
end
pass 5 "decompose user"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:267:269
dcllen 4
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:267:269
dcllen 4
end
pass 7 "opt"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:267:269
dcllen 4
end
pass 8 "zero arg cse"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:267:269
dcllen 4
end
pass 9 "opt deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:267:269
dcllen 4
end
pass 10 "generic cse"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 11 "phiopt"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 12 "gcse deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 13 "nilcheckelim"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 14 "prove"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 15 "divisible"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 16 "divmod"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 17 "middle opt"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 18 "known bits"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 19 "early fuse"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticLECall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:0:0 1 v6
v v10 StaticLECall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:0:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v13,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 20 "expand calls"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 2 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v13 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t19 0 a3 p2:269:2:1:0 0 v5,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 21 "decompose builtin"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 2 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v13 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t19 0 a3 p2:269:2:1:0 0 v5,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 22 "softfloat"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 2 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v13 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t19 0 a3 p2:269:2:1:0 0 v5,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 23 "branchelim"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 2 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v13 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t19 0 a3 p2:269:2:1:0 0 v5,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 24 "late opt"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v4,v5,v13,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 25 "dead auto elim"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v4,v5,v13,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 26 "sccp"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v4,v5,v13,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 27 "generic deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v4,v5,v13,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 28 "late fuse"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v4,v5,v13,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 29 "check bce"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v4,v5,v13,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 30 "dse"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v4,v5,v13,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 31 "memcombine"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v4,v5,v13,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 32 "writebarrier"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 Const64 t11 32 - p0:0:0:0:0 1 -
v v6 StaticCall t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 StaticCall t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 1 v10
v v14 Rsh32Ux64 t2 0 - p2:268:4:0:0 1 v8,v12
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts 32=v9
freev v4,v5,v13,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 33 "lower"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 34 "addressing modes"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 35 "late lower"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 36 "pair"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 38 "lowered cse"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 39 "elim unread autos"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 41 "lowered deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 42 "checkLower"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 43 "loop invariant"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 45 "tighten"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 46 "late deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 47 "critical"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 48 "phi tighten"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 49 "likelyadjust"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 2:267:269
dcllen 4
end
pass 50 "layout"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 2:267:269
fstate laidout
dcllen 4
end
pass 51 "schedule"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 2:267:269
fstate scheduled,laidout
dcllen 4
end
pass 52 "late nilcheck"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 2:267:269
fstate scheduled,laidout
dcllen 4
end
pass 53 "flagalloc"
f b1 t1 a1 15 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v9 ARM64MOVDconst t11 32 - p0:0:0:0:0 1 -
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v9,v7
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v8
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev v13,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 2:267:269
fstate scheduled,laidout
dcllen 4
end
pass 54 "regalloc"
aux a1 call "AuxCall{main.u32rand}" a2 1 0 1 8 0 0 1
abiparam out 0 t2 a3 0 -1
callreg 0:1 - 0 -
aux a4 call "AuxCall{math/rand.Uint32}" a5 1 0 1 8 0 0 1
abiparam out 0 t2 - 0 -1
callreg - 0:1 7fffffff97ffffff -
aux a6 call "AuxCall{math/rand.Intn}" a7 1 1 1 8 8 1 1
abiparam in 0 t11 - 0 0
abiparam out 0 t11 - 0 -1
callreg 0:1 0:1 7fffffff97ffffff -
f b1 t1 a1 16 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v2 StoreReg t2 0 - p2:267:25:1:0 1 v8
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v13 ARM64MOVDconst t11 32 - p2:268:22:2:0 1 -
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v13,v7
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v16 LoadReg t2 0 - p2:268:4:2:0 1 v2
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v16
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 2:267:269
fstate scheduled,laidout
regalloc 17 v2:@a8/t2/0/-/0,v4:R1,v5:R1,v6:[R0],v8:R0,v10:[R0],v12:R0,v13:R0,v14:R0,v15:[],v16:R1
dcllen 4
end
pass 55 "loop rotate"
f b1 t1 a1 16 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v2 StoreReg t2 0 - p2:267:25:1:0 1 v8
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v13 ARM64MOVDconst t11 32 - p2:268:22:2:0 1 -
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v13,v7
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v16 LoadReg t2 0 - p2:268:4:2:0 1 v2
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v16
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 2:267:269
fstate scheduled,laidout
regalloc 17 v2:@a8/t2/0/-/0,v4:R1,v5:R1,v6:[R0],v8:R0,v10:[R0],v12:R0,v13:R0,v14:R0,v15:[],v16:R1
dcllen 4
end
pass 56 "trim"
f b1 t1 a1 16 1
b b1 Ret p2:269:2:1:0 0 0 - v15 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t33 0 a4 p2:267:25:1:0 2 v1
v v8 SelectN t2 0 - p2:267:25:1:0 1 v6
v v2 StoreReg t2 0 - p2:267:25:1:0 1 v8
v v7 SelectN t28 1 - p2:267:25:0:0 1 v6
v v13 ARM64MOVDconst t11 32 - p2:268:22:2:0 1 -
v v10 ARM64CALLstatic t34 8 a6 p2:268:22:1:0 2 v13,v7
v v12 SelectN t11 0 - p2:268:22:1:0 2 v10
v v11 SelectN t28 1 - p2:268:22:0:0 1 v10
v v16 LoadReg t2 0 - p2:268:4:2:0 1 v2
v v4 ARM64MOVWUreg t10 0 - p2:268:4:0:0 1 v16
v v5 ARM64SRL t2 0 - p2:268:4:0:0 1 v4,v12
v v3 ARM64CMPconst t29 64 - p2:268:4:0:0 1 v12
v v14 ARM64CSEL0 t2 4582 - p2:268:4:0:0 1 v5,v3
v v15 MakeResult t33 0 - p2:269:2:1:0 1 v14,v11
names s1
named s1 v8,v14
splits -
canon a8/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 2:267:269
fstate scheduled,laidout
regalloc 17 v2:@a8/t2/0/-/0,v4:R1,v5:R1,v6:[R0],v8:R0,v10:[R0],v12:R0,v13:R0,v14:R0,v15:[],v16:R1
dcllen 4
end
frontend
end
ptrcache t2,t5,t6,t7,t8,t11,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t2,t7,t10,t11,t14,t15,t25,t26,t12,t13,t3,t17,t18,t19,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t33,t34
eof
"#

/-- `test/ken_divconst/main/u32rand,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "u32rand" 1
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
type t1 4 4 0 0 - "uint32"
name n1 "~r0" PPARAMOUT t1 1 "main.~r0" 0 a3
name n2 "a" PAUTO t1 1 "main.a" 0 a8
name n3 ".autotmp_2" PAUTO t1 3 "main..autotmp_2" 0 -
type t2 8 8 0 0 - "int"
name n4 ".autotmp_3" PAUTO t2 3 "main..autotmp_3" 0 -
in n1 0 outregs
in n2 0 used
in n3 0 used,autotmp
in n4 0 used,autotmp
out n2 -4 used
opt n4 0 autotmp
opt n3 0 autotmp
opt n1 0 outregs
stack 8 0 8
end
genin
posbase p2 "./divconst.go" 1 1 -1 1 "./divconst.go" "./divconst.go" 1 1
sym y1 "main.u32rand" 1
curfn p2:266:6:0:0 0 0
regargs -
text y1 0 0 0 0 266 200080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "math/rand.Uint32" 1
sym y4 "main.a" 0
sym y5 "math/rand.Intn" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i0 0 0 p2:266:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:266:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:266:6:0:0
p 3 3 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p2:267:25:1:0
p 4 4 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:267:25:1:0
p 5 5 0 0 0 - MOVW 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/AUTO/0/-4/y4/- 0 0 p2:267:25:2:0
p 6 6 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/32/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:268:22:1:0
p 7 7 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:268:22:1:0
p 8 8 0 0 0 - MOVWU 0 MEM/8383/0/0/AUTO/0/-4/y4/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:268:4:2:0
p 9 9 0 0 0 - LSR 0 REG/8192/0/0/NONE/0/0/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:268:4:2:0
p 10 10 0 0 0 - CMP 0 CONST/0/0/0/NONE/0/64/-/- 8192 - _ 0 0 p2:268:4:2:0
p 11 11 0 0 0 - CSEL 0 SPECIAL/0/0/0/NONE/0/131/-/- 8193 0:REG/8223/0/0/NONE/0/0/-/- REG/8192/0/0/NONE/0/0/-/- 0 0 p2:268:4:2:0
p 12 12 0 0 0 - RET 0 _ 0 - _ 0 0 p2:269:2:1:0
p 13 13 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 266 200080
funcaux y2 y2 - - - - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4
autot -
dbgentry 1
dbgslot 0 n2 t1 0
dbgvar 0 n2 0
dbgloc 0 1:8:1:13:50,1:13:-1:-30000:9174
dbgregout n1
dbgpc 1:8:5,1:13:7
end
asm
sym y6 "runtime.morestack_noctxt" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i0 0 0 p2:266:6:0:0
p 14 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:266:6:0:0
p 15 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:266:6:0:0
p 16 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:266:6:0:0
p 17 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@26 0 0 p2:266:6:0:0
p 18 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:266:6:0:0
p 19 12 32 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-32/-/- 0 0 p2:266:6:0:1
p 20 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:266:6:0:0
p 21 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:266:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:266:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:266:6:0:0
p 3 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p2:267:25:1:0
p 4 24 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y3/- 0 0 p2:267:25:1:0
p 5 28 0 0 371 - MOVW 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/AUTO/49/-4/y4/- 0 0 p2:267:25:2:0
p 6 32 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/32/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:268:22:1:0
p 7 36 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y5/- 0 0 p2:268:22:1:0
p 8 40 0 0 388 - MOVWU 0 MEM/0/0/0/AUTO/49/-4/y4/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:268:4:2:0
p 9 44 0 0 272 - LSR 0 REG/8192/0/0/NONE/2/0/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:268:4:2:0
p 10 48 0 0 96 - CMP 0 CONST/0/0/0/NONE/17/64/-/- 8192 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:268:4:2:0
p 11 52 0 0 102 - CSEL 0 SPECIAL/0/0/0/NONE/11/131/-/- 8193 0:REG/8223/0/0/NONE/3/0/-/- REG/8192/0/0/NONE/2/0/-/- 0 0 p2:268:4:2:0
p 12 56 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:269:2:1:0
p 22 60 -32 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/32/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:269:2:1:0
p 23 64 32 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:269:2:1:0
p 24 68 -32 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:269:2:1:0
p 25 68 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:266:6:0:0
p 26 68 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:266:6:0:0
p 27 68 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:266:6:0:0
p 28 72 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y6/- 0 0 p2:266:6:0:0
p 29 76 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:266:6:0:0
p 30 76 32 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@14 0 0 p2:266:6:0:0
fn y1 0 24 0 0 266 200080
funcaux y2 y2 - - - - -
text 80 0 900b40f9ff6330ebe9010054fe0f1ef8fd831ff8fd2300d100000094e01700b9e0037bb200000094e11740b92124c09a1f0001f120309f9afd835ff8fe0742f8c0035fd6e3031eaa00000094edffff17 3
reloc 24 4 R_CALLARM64 0 y3
reloc 36 4 R_CALLARM64 0 y5
reloc 72 4 R_CALLARM64 0 y6
pcln y9 y10 y11 y12 y7,y8 y2,y2
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y7 SRODATA 11 1 28000 00010102020e0102020100 0
data y8 SRODATA 7 1 28000 0006020b010300 0
data y9 SRODATA 7 1 28000 0204400c3f0400 0
data y10 SRODATA 3 1 28000 041400 0
data y11 SRODATA 12 1 28000 960406020202060203050300 0
data y12 SRODATA 3 1 28000 001400 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.uint32" 0
sym y18 "type:uint32" 0
dwfn y13 y14 y15 - y16 "main.u32rand" 1:266 1 0 1 26
dwdcl n2
dwclosure 0 -
dwparents -
dwparams n1
dwname n2 1 1 0 0 0 0 -4 0 - - "uint32" 0 0 1 p2:267:2:0:0
dwname n4 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p2:268:22:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "uint32" 0 0 1 p2:267:25:0:0
dwname n1 1 0 0 0 0 0 0 1 - - "uint32" 0 0 1 p2:266:16:0:0
var 0 0 "~r0" 5 1 1 0 0 0 y17 "./divconst.go" 266 16 0 0 0 0 -
var 1 0 "a" 52 1 0 0 0 -12 y17 "./divconst.go" 267 2 0 1 0 0 v0
scope 0 0 - 0,1
data y13 SDWARFFCN 52 0 0 036d61696e2e75333272616e64000050019c020000008a02012e7e723000018a0200000000002761008b02000000000000000000 5
reloc 0 0 R_USETYPE 0 y18
reloc 14 1 R_DWTXTADDR_U1 0 y1
reloc 33 4 R_DWARFSECREF 0 y17
reloc 43 4 R_DWARFSECREF 0 y17
reloc 47 4 R_DWARFSECREF 0 y14
data y14 SDWARFLOC 14 0 0 0100041c24015004245002917400 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y16 SDWARFLINES 34 0 0 00090200000000000000000402038402140a878806370638065f06b084020c000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`) with P0' (`p0PrimeSyms`, as `gen-check`
runs G56 to G66). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) := do
  let (lc, ps, bs, g) ← GenG2.load fSsa fProg
  let (syms', ps') ← GoFV.Asm.p0PrimeSyms g.syms ps
  return (lc, ps', bs, { g with syms := syms' })

/-- `runLoc`'s context of `u32rand`. -/
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

/-- `b1`, the only block, whose value 10 is `v4 = MOVWUreg v16`. -/
def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0''s layout: the Prog with ID `n` at `0x10000 + 4n`, a 24-byte frame with 8 bytes of extra
space, every symbol at `symA`; `NAME_AUTO` `-4` is `SP + 12`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 24 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, the home slots at their frame operands and the PC table of `checkG66`; not G48's mode
(`outSP = false`). -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := GenG2.sp0,
    slot := fun k =>
      if k ∈ homeSlots lc then (g.slotOp k).map (fun p => frameOff L p.1 p.2) else none,
    g := 0x9000, lr := 0, fp := 0, framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `uint32` the reload `v16` gave. -/
def X : BitVec 32 := 0xDEADBEEF

/-- A state before `v4`: `X` in `R1` (Go register 1, `v16`'s home), every other register
`poison`, no slot, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 17 none, args := [], mem0 := GenG2.mem0, images := #[] },
    regs := Array.ofFn (n := 64) fun i => if i.val = 1 then .int .w32 X else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v4`: the activation's `g` and `FP`, the PC of `v4`, `X` zero-extended in
`X1` (as genssa's `MOVWU` reload left it), the memory 0. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else
      if k = 1 then X.setWidth 64 else 0,
    sp := GenG2.sp0, v := fun _ => 0,
    nzcv := ⟨false, false, false, false⟩, pc := E.pcOf 1 10, mem := fun _ => 0 }

/-- The home slots lie above the saved `LR` and below `2^64`. -/
def slotsFit : Bool :=
  (homeSlots lc).all fun k =>
    match g.slotOp k with
    | some (nc, off) => decide (8 ≤ frameOff L nc off) &&
        decide (GenG2.sp0.toNat + (frameOff L nc off).toNat + 8 ≤ 2 ^ 64)
    | none => true

/-- After `v4`: `R1` holds the `uint64` zero extension of `X`. -/
def holdsX (s : LocState) : Bool :=
  match s.regs[1]? with
  | some (Val.int .w64 n) => n == X.setWidth 64
  | _ => false

theorem holdsX_spec {s : LocState} (H : holdsX s = true) :
    s.regs[1]? = some (.int .w64 (X.setWidth 64)) := by
  unfold holdsX at H
  split at H
  · rename_i n hn
    simp only [beq_iff_eq] at H
    rw [hn, H]
  · cases H

/-- What compiled evaluation checks on `u32rand`: it holds an arm64 op; on P0', `checkG66`
accepts it with `tab` and `kt` and `checkG65` does not; it accesses no frame variable, its home
slots fit and it needs no G48 mode; G2's symbols have no float constant; `b1` holds `v4`
(`MOVWUreg v16`, an extension genssa elides, `elide66b`) at index 10, where G35's table is the
reload's entry `(R1, 32, unsigned)` and the class table gives `R1` class 32; `stepLoc` runs `v4`
from `s0` to `R1` holding the zero extension of `X`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG66 lc0 ps bs g).toOption == some (tab, kt) && (checkG65 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && slotsFit && needs48 lc == false &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 4).isSome && blk.values[10]? == some 4 &&
    (val 4).op == .ARM64MOVWUreg && (val 4).id == 4 && elide66b lc (val 4) == some (32, false) &&
    (constRo (symNames g)).isEmpty &&
    uL35 lc (uIn35 lc 1) blk 10 == [(1, 32, false)] && (kAt lc kt 1 blk 10).get 1 == some 32 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 4)) holdsX

theorem g66b_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG66 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG65 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ slotsFit = true ∧ needs48 lc = false ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 4 = some (val 4) ∧ blk.values[10]? = some 4 ∧
      (val 4).op = .ARM64MOVWUreg ∧ (val 4).id = 4 ∧ elide66b lc (val 4) = some (32, false) ∧
      (constRo (symNames g)).isEmpty = true ∧
      uL35 lc (uIn35 lc 1) blk 10 = [(1, 32, false)] ∧ (kAt lc kt 1 blk 10).get 1 = some 32 ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 4)) holdsX = true := by
  have hf := g66b_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h65, hav, hfit, h48, hm1, hbs, hvs, hi, hop, hid, hel, hro, hu, hk1,
    hrun⟩ := hf
  refine ⟨hl, ?_, h65, hav, hfit, h48, hm1, ?_, ?_, hi, hop, hid, hel, hro, hu, hk1, hrun⟩
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
    (r = 1 ∧ x = .int .w32 X) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1
      exact .inl ⟨h1, h.symm⟩
    · exact .inr h.symm
  · cases h

/-- `R1` is Go register 1, the obj register `X1`. -/
theorem objX1 : objX? 1 = some (BitVec.ofNat 5 1) := by decide

theorem objV1 : objV? 1 = none := by decide

theorem locMatch0 : LocMatch E s0 1 10 m0 where
  regs := by
    intro r x hx
    rcases s0_regs hx with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rw [objX1] at hk
        cases hk
        show ((m0.x (BitVec.ofNat 5 1)).setWidth 32 : BitVec 32) = X
        decide
      · rw [objV1] at hk
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

theorem g66Inv0 (hk1 : (kAt lc kt 1 blk 10).get 1 = some 32) :
    G3Inv E lc (kAt lc kt 1 blk 10) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, GenG2.keys0, GenG2.sep0⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [hk1] at hc
      cases hc
      show kNarrow 32 32 = true
      decide
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- G35's table before `v4`, the reload's entry `(R1, 32, unsigned)`, holds at `m0`: `X1` is the
zero extension of its low 32 bits. -/
theorem uokl0 : UOKL m0 [(1, 32, false)] := by
  intro e he
  simp only [List.mem_singleton] at he
  subst he
  intro k hk hobj
  rw [objX1] at hobj
  have hk1 : k = 1 := by
    have := congrArg BitVec.toNat (Option.some.inj hobj)
    simp at this
    omega
  subst hk1
  show m0.x (BitVec.ofNat 5 1) = _
  decide

/-! ## `v4`: `MOVWUreg v16`, elided -/

/-- The per-value premises of G54 on `v4`, `MOVWUreg`: none of them applies. -/
theorem pre54 (hop : (val 4).op = .ARM64MOVWUreg) : G54Pre lc s0 (val 4) := by
  have hne : ∀ o : Op, o ≠ .ARM64MOVWUreg → (val 4).op ≠ o := fun o h h' => h (h'.symm.trans hop)
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

/-- **G66b on `u32rand`** (`v4 = MOVWUreg v16`, the zero extension of a `MOVWU` reload, which
genssa elides: `elide66b`): `checkG65` rejects the function and `checkG66` accepts it. From a state
with the `uint32` `X` in `R1`, `stepLoc` runs `v4` to `R1` holding its `uint64` zero extension, and
`g66_value` (at the mode `false`, the function needing no G48 mode), from a machine `m0` whose `X1`
holds that extension (G35's entry of the reload), relates it to a machine run to a state whose `X1`
is related to that `uint64`, under an activation extending `E` that is again a `G49Env`. -/
theorem genG66b_witness :
    (checkG65 lc0 ps bs g).toOption = none ∧ elide66b lc (val 4) = some (32, false) ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 4) = .ok s1 ∧
        s1.regs[1]? = some (.int .w64 (X.setWidth 64)) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 11 m1 ∧
        ValRel E1.ι (.int .w64 (X.setWidth 64)) (m1.x (BitVec.ofNat 5 1)) := by
  obtain ⟨hl, hc, h65, hav, hfit, h48, hm1, hb, hv4, hi, hop, hid, hel, hro, hu, hk1, hrun⟩ :=
    facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr1 : s1.regs[1]? = some (.int .w64 (X.setWidth 64)) := holdsX_spec hr
  have hE := g66Env hc hl hav hfit
  have hne : ∀ o : Op, o ≠ .ARM64MOVWUreg → (val 4).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  -- `g66_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 4 = some (val 4) := by
    rw [← liveCtx_ctx (lc := lc0)]; exact hv4
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -, -⟩ := g66_value (H := GenG2.H0) (env := GenG2.env)
    (osp := false) hc hE hl0 hm0 hb0 hi hv0 (by rw [hop]; rfl) locMatch0 (g66Inv0 hk1)
    (fun h => by cases h) (fun h => by cases h)
    (fun h => by
      have h' : needs48 lc = true := h
      rw [h48] at h'
      cases h')
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 10); rw [hu]; exact uokl0)
    (pre54 hop) (ro0 hro)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => by cases h) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide)))
    ⟨fun h => absurd h (hne _ (by decide)), fun h => absurd h (hne _ (by decide))⟩ hs1
  refine ⟨h65, hel, s1, E1, m1, hs1, hr1, hx1, hE1, hp1, hm1', ?_⟩
  exact (hm1'.regs 1 _ hr1).1 _ objX1

end GoFV.Proof.Witness.GenG66b
