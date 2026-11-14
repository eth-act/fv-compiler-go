import GoFV.Proof.Gen.G63
import GoFV.Proof.Witness.GenG14
import GoFV.Asm.ConstLoad

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G63 of the genssa validator on `doprint` of `test/ken_cplx0`

`test/ken_cplx0/main/doprint,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`), loaded on P0'
(`p0PrimeSyms`, as `gen-check` runs G56 to G63):

```go
func doprint(c complex128) { println(c) }
```

`c` arrives in `F0` and `F1` (`v15`, `v16 = ArgFloatReg`). Block `b1` (the entry) spills both
halves to the slots of `c`'s pieces before the first call (`v2 = StoreReg v15`, `FMOVD F0,
c+0(FP)`; `v4 = StoreReg v16`, `FMOVD F1, c+8(FP)`) and reloads them after it (`v3`, `v5 =
LoadReg`, `FMOVD c+0(FP), F0` …). G62 spills X registers only (`argument v# in register #`,
`writes register #`), so `checkG62` rejects the function; `checkG63` accepts it with the PC table
`tab` and the class table `kt`. The function needs no G48 mode (`needs48 lc = false`).

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g63_facts`),
`stepLoc` runs `v2` (value 2 of `b1`) from a state `s0` with the `float64` `1.5` (bits
`0x3FF8000000000000`) in `F0` and no slot to the slot of `c`'s first piece holding those bits. On
a framed activation with `G49Env` (the slot at `SP + 24`; not G48's mode, `outSP = false`), from a
machine `m0` holding the bits in the low 64 bits of `V0`, `g63_value` at the mode `false` relates
that step to the machine, which runs the `FMOVD` (`genG63_witness`): the machine's word at
`SP + 24` is `0x3FF8000000000000`.
-/

namespace GoFV.Proof.Witness.GenG63

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/ken_cplx0/main/doprint,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "doprint" 1 0 0
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
type t2 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t1 FUNC 8 8 8 hasptr,direct "func(complex128)" "func(complex128)" 0 1 0
field 0 "c" t2 ? 0
aux a2 sym "main.doprint" "main.doprint" 1 - 0 - - - - 0
posbase p2 "./cplx0.go" 1 1 -1
aux a3 name "c" "c" PPARAM t2 0 1 used p2:18:14:0:0
aux a1 call "AuxCall{main.doprint}" a2 1 1 0 8 16 2 0
abiparam in 0 t2 a3 16,17 0
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
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
type t17 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t18 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t19 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t21 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t12
type t22 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t16
type t23 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t13
type t24 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t14
type t25 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t18
type t26 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t27 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t28 SSA ? ? ? - "mem" ""
type t29 SSA ? ? ? - "flags" ""
type t30 SSA ? ? ? - "void" ""
type t31 SSA 16 8 ? - "int128" ""
type t32 RESULTS ? ? ? - "mem" "" 1 t28
type t33 PTR 8 8 8 hasptr,direct,comparable "*complex128" "*complex128" t2
aux a5 sym "runtime.printlock" "runtime.printlock" 1 - 0 - - - - 0
aux a4 call "AuxCall{runtime.printlock}" a5 1 0 0 8 0 0 0
aux a7 sym "runtime.printcomplex128" "runtime.printcomplex128" 1 - 0 - - - - 0
aux a6 call "AuxCall{runtime.printcomplex128}" a7 1 1 0 8 16 2 0
abiparam in 0 t2 - 16,17 0
aux a9 sym "runtime.printnl" "runtime.printnl" 1 - 0 - - - - 0
aux a8 call "AuxCall{runtime.printnl}" a9 1 0 0 8 0 0 0
aux a11 sym "runtime.printunlock" "runtime.printunlock" 1 - 0 - - - - 0
aux a10 call "AuxCall{runtime.printunlock}" a11 1 0 0 8 0 0 0
slot s1 a3 t2 0 - 0
f b1 t1 a1 14 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t14,UInt=t15,Uintptr=t16,String=t17,BytePtr=t18,Int32Ptr=t19,UInt32Ptr=t20,IntPtr=t21,UintptrPtr=t22,Float32Ptr=t23,Float64Ptr=t24,BytePtrPtr=t25,Complex64=t26,Complex128=t2,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:0:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
dcllen 1
end
pass 1 "number lines"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 2:18:18
dcllen 1
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 2:18:18
dcllen 1
end
pass 3 "early deadcode"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:18:18
dcllen 1
end
pass 4 "short circuit"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:18:18
dcllen 1
end
pass 5 "decompose user"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:18:18
dcllen 1
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:18:18
dcllen 1
end
pass 7 "opt"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:18:18
dcllen 1
end
pass 8 "zero arg cse"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:18:18
dcllen 1
end
pass 9 "opt deadcode"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:18:18
dcllen 1
end
pass 10 "generic cse"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 11 "phiopt"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 12 "gcse deadcode"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 13 "nilcheckelim"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 14 "prove"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 15 "divisible"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 16 "divmod"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 17 "middle opt"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 18 "known bits"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 19 "early fuse"
f b1 t1 a1 14 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:18:6:2:0 1 -
v v6 StaticLECall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticLECall t32 16 a6 p2:18:37:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticLECall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticLECall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 20 "expand calls"
aux a12 nameoff "c+0" a3 0
aux a13 nameoff "c+8" a3 8
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ComplexMake t2 0 - p2:18:41:2:0 2 v15,v16
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v17,v18,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v4 SB t16 0 - p0:0:0:0:0 0 -
v v3 SP t16 0 - p0:0:0:0:0 1 -
v v2 OffPtr t33 0 - p0:0:0:0:0 0 v3
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
v v17 ComplexReal t14 0 - p2:18:37:0:0 1 v5
v v18 ComplexImag t14 0 - p2:18:37:2:0 1 v5
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 21 "decompose builtin"
slot s2 a3 t14 0 - 0
slot s3 a3 t14 8 - 0
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ComplexMake t2 0 - p2:18:41:2:0 0 v15,v16
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v4 SB t16 0 - p0:0:0:0:0 0 -
v v3 SP t16 0 - p0:0:0:0:0 1 -
v v2 OffPtr t33 0 - p0:0:0:0:0 0 v3
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 2 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 2 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts 0=v2
freev v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 22 "softfloat"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ComplexMake t2 0 - p2:18:41:2:0 0 v15,v16
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v4 SB t16 0 - p0:0:0:0:0 0 -
v v3 SP t16 0 - p0:0:0:0:0 1 -
v v2 OffPtr t33 0 - p0:0:0:0:0 0 v3
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 2 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 2 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts 0=v2
freev v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 23 "branchelim"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ComplexMake t2 0 - p2:18:41:2:0 0 v15,v16
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v4 SB t16 0 - p0:0:0:0:0 0 -
v v3 SP t16 0 - p0:0:0:0:0 1 -
v v2 OffPtr t33 0 - p0:0:0:0:0 0 v3
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 2 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 2 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts 0=v2
freev v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 24 "late opt"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 25 "dead auto elim"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 26 "sccp"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 27 "generic deadcode"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 28 "late fuse"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 29 "check bce"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 30 "dse"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 31 "memcombine"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 32 "writebarrier"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 StaticCall t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 StaticCall t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 StaticCall t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 StaticCall t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 33 "lower"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 34 "addressing modes"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 35 "late lower"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 36 "pair"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:18:18
dcllen 1
end
pass 38 "lowered cse"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
dcllen 1
end
pass 39 "elim unread autos"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
dcllen 1
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
dcllen 1
end
pass 41 "lowered deadcode"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
dcllen 1
end
pass 42 "checkLower"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
dcllen 1
end
pass 43 "loop invariant"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
dcllen 1
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
dcllen 1
end
pass 45 "tighten"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
dcllen 1
end
pass 46 "late deadcode"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
dcllen 1
end
pass 47 "critical"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
dcllen 1
end
pass 48 "phi tighten"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
dcllen 1
end
pass 49 "likelyadjust"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
dcllen 1
end
pass 50 "layout"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
fstate laidout
dcllen 1
end
pass 51 "schedule"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
fstate scheduled,laidout
dcllen 1
end
pass 52 "late nilcheck"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
fstate scheduled,laidout
dcllen 1
end
pass 53 "flagalloc"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v15,v16,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v18,v17
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
fstate scheduled,laidout
dcllen 1
end
pass 54 "regalloc"
aux a6 call "AuxCall{runtime.printcomplex128}" a7 1 1 0 8 16 2 0
abiparam in 0 t2 - 16,17 0
callreg 0:80000000,1:100000000 - 7fffffff97ffffff -
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
v v2 StoreReg t14 0 - p2:18:41:2:0 1 v15
v v4 StoreReg t14 0 - p2:18:41:2:0 1 v16
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v3 LoadReg t14 0 - p2:18:37:2:0 1 v2
v v5 LoadReg t14 0 - p2:18:37:2:0 1 v4
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v3,v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v17,v18
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
fstate scheduled,laidout
regalloc 17 v2:@a3/t14/0/-/0,v3:F0,v4:@a3/t14/8/-/0,v5:F1,v8:[],v15:F0,v16:F1
dcllen 1
end
pass 55 "loop rotate"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
v v2 StoreReg t14 0 - p2:18:41:2:0 1 v15
v v4 StoreReg t14 0 - p2:18:41:2:0 1 v16
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v3 LoadReg t14 0 - p2:18:37:2:0 1 v2
v v5 LoadReg t14 0 - p2:18:37:2:0 1 v4
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v3,v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v17,v18
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
fstate scheduled,laidout
regalloc 17 v2:@a3/t14/0/-/0,v3:F0,v4:@a3/t14/8/-/0,v5:F1,v8:[],v15:F0,v16:F1
dcllen 1
end
pass 56 "trim"
f b1 t1 a1 18 1
b b1 Ret p2:18:41:0:0 0 0 - v14 - -
v v15 ArgFloatReg t14 0 a12 p2:18:41:2:0 1 -
v v16 ArgFloatReg t14 1 a13 p2:18:41:2:0 1 -
v v2 StoreReg t14 0 - p2:18:41:2:0 1 v15
v v4 StoreReg t14 0 - p2:18:41:2:0 1 v16
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 0 a4 p2:18:37:1:0 1 v1
v v7 SelectN t28 0 - p2:18:37:0:0 1 v6
v v3 LoadReg t14 0 - p2:18:37:2:0 1 v2
v v5 LoadReg t14 0 - p2:18:37:2:0 1 v4
v v8 ARM64CALLstatic t32 16 a6 p2:18:37:0:0 1 v3,v5,v7
v v9 SelectN t28 0 - p2:18:37:0:0 1 v8
v v10 ARM64CALLstatic t32 0 a8 p2:18:37:0:0 1 v9
v v11 SelectN t28 0 - p2:18:37:0:0 1 v10
v v12 ARM64CALLstatic t32 0 a10 p2:18:37:0:0 1 v11
v v13 SelectN t28 0 - p2:18:37:0:0 1 v12
v v14 MakeResult t32 0 - p2:18:41:0:0 1 v13
names s2,s3
named s2 v15
named s3 v16
splits s1/0/t14=s2,s1/8/t14=s3
canon a3/t2/0/-/0=s1
consts -
freev v17,v18
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a12:2,a13:3
cache linestarts 2:18:18
fstate scheduled,laidout
regalloc 17 v2:@a3/t14/0/-/0,v3:F0,v4:@a3/t14/8/-/0,v5:F1,v8:[],v15:F0,v16:F1
dcllen 1
end
frontend
end
ptrcache t5,t6,t7,t8,t10,t12,t13,t14,t16,t17,t18,t25
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t12,t15,t16,t26,t2,t13,t14,t3,t18,t19,t20,t21,t22,t33,t23,t24,t25,t1,t17,t27,t28,t30,t29,t31,t32
eof
"#

/-- `test/ken_cplx0/main/doprint,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "doprint" 1
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
type t1 16 8 0 0 - "complex128"
name n1 "c" PPARAM t1 1 "main.c" 0 a3
in n1 0 used
out n1 0 used
stack 0 0 8
end
genin
posbase p2 "./cplx0.go" 1 1 -1 1 "./cplx0.go" "./cplx0.go" 1 1
type t2 8 8 0 0 - "float64"
sym y1 "main.doprint" 1
curfn p2:18:6:0:0 0 0
regargs 8224:0:t2,8225:8:t2
text y1 0 0 0 0 18 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "main.doprint.arginfo1" 0
sym y4 "main.doprint.argliveinfo" 0
sym y5 "main.c" 0
sym y6 "runtime.printlock" 1
sym y7 "runtime.printcomplex128" 1
sym y8 "runtime.printnl" 1
sym y9 "runtime.printunlock" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i16 0 0 p2:18:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:18:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:18:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:18:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:18:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:18:6:2:0
p 6 6 0 0 0 - FMOVD 0 REG/8224/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/PARAM/0/0/y5/- 0 0 p2:18:41:1:0
p 7 7 0 0 0 - FMOVD 0 REG/8225/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/PARAM/0/8/y5/- 0 0 p2:18:41:2:0
p 8 8 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:18:41:2:0
p 9 9 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p2:18:37:1:0
p 10 10 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p2:18:37:1:0
p 11 11 0 0 0 - FMOVD 0 MEM/8383/0/0/PARAM/0/0/y5/- 0 - REG/8224/0/0/NONE/0/0/-/- 0 0 p2:18:37:2:0
p 12 12 0 0 0 - FMOVD 0 MEM/8383/0/0/PARAM/0/8/y5/- 0 - REG/8225/0/0/NONE/0/0/-/- 0 0 p2:18:37:2:0
p 13 13 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p2:18:37:2:0
p 14 14 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y8/- 0 0 p2:18:37:2:0
p 15 15 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y9/- 0 0 p2:18:37:2:0
p 16 16 0 0 0 - RET 0 _ 0 - _ 0 0 p2:18:41:0:0
p 17 17 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 18 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8224 8225 FSTPD FLDPD
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t2 0
dbgslot 1 n1 t2 8
dbgvar 0 n1 0,1
dbgloc 0 1:-10000:1:6:9040930890419308,1:6:-1:-30000:9108930891109308
dbgregout -
dbgpc 1:6:11
end
asm
sym y10 "runtime.morestack_noctxt" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i16 0 0 p2:18:6:0:0
p 18 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:18:6:0:0
p 19 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:18:6:0:0
p 20 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:18:6:0:0
p 21 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@30 0 0 p2:18:6:0:0
p 22 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:18:6:0:0
p 23 12 32 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-32/-/- 0 0 p2:18:6:0:1
p 24 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:18:6:0:0
p 25 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:18:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:18:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:18:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:18:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:18:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:18:6:2:0
p 6 24 0 0 140 - FMOVD 0 REG/8224/0/0/NONE/5/0/-/- 0 - MEM/0/0/0/PARAM/48/0/y5/- 0 0 p2:18:41:1:0
p 7 28 0 0 140 - FMOVD 0 REG/8225/0/0/NONE/5/0/-/- 0 - MEM/0/0/0/PARAM/47/8/y5/- 0 0 p2:18:41:2:0
p 8 32 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:18:41:2:0
p 9 32 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p2:18:37:1:0
p 10 32 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y6/- 0 0 p2:18:37:1:0
p 11 36 0 0 153 - FMOVD 0 MEM/0/0/0/PARAM/48/0/y5/- 0 - REG/8224/0/0/NONE/5/0/-/- 0 0 p2:18:37:2:0
p 12 40 0 0 153 - FMOVD 0 MEM/0/0/0/PARAM/47/8/y5/- 0 - REG/8225/0/0/NONE/5/0/-/- 0 0 p2:18:37:2:0
p 13 44 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y7/- 0 0 p2:18:37:2:0
p 14 48 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y8/- 0 0 p2:18:37:2:0
p 15 52 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y9/- 0 0 p2:18:37:2:0
p 16 56 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:18:41:0:0
p 26 60 -32 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/32/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:18:41:0:0
p 27 64 32 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:18:41:0:0
p 28 68 -32 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:18:41:0:0
p 29 68 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:18:6:0:0
p 30 68 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:18:6:0:0
p 31 68 0 0 436 - FSTPD 0 REGREG/8224/0/0/NONE/7/8225/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p2:18:6:0:0
p 32 72 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:18:6:0:0
p 33 76 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y10/- 0 0 p2:18:6:0:0
p 34 80 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:18:6:0:0
p 35 80 0 0 245 - FLDPD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REGREG/8224/0/0/NONE/7/8225/-/- 0 0 p2:18:6:0:0
p 36 84 32 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@18 0 0 p2:18:6:0:0
fn y1 16 24 0 0 18 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8224 8225 FSTPD FLDPD
funcaux y2 y2 - - y3 y4 -
text 96 0 900b40f9ff6330ebe9010054fe0f1ef8fd831ff8fd2300d1e01700fde11b00fd00000094e01740fde11b40fd000000940000009400000094fd835ff8fe0742f8c0035fd6e087006de3031eaa00000094e087406debffff170000000000000000 5
reloc 32 4 R_CALLARM64 0 y6
reloc 44 4 R_CALLARM64 0 y7
reloc 48 4 R_CALLARM64 0 y8
reloc 52 4 R_CALLARM64 0 y9
reloc 76 4 R_CALLARM64 0 y10
pcln y15 y16 y17 y18 y11,y12,y13,y14 y2,y2,_,_,_,y3,y4
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 7 1 8000 fe00080808fdff 0
data y4 SDATA 2 1 8000 0000 0
data y11 SRODATA 11 1 28000 00010102020e0103020400 0
data y12 SRODATA 7 1 28000 00080209010700 0
data y13 SRODATA 0 1 28000 - 0
data y14 SRODATA 7 1 28000 00060402031000 0
data y15 SRODATA 7 1 28000 0204400c3f0800 0
data y16 SRODATA 3 1 28000 041800 0
data y17 SRODATA 3 1 28000 261800 0
data y18 SRODATA 3 1 28000 001800 0
end
dwarf
sym y19 "" 0
sym y20 "" 0
sym y21 "" 0
sym y22 "go:info.main.doprint$abstract" 0
sym y23 "" 0
sym y24 "go:info.complex128" 0
dwfn y19 y20 y21 y22 y23 "main.doprint" 1:18 1 0 1 2
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwprecursor y1 y22 n1
dwname n1 1 1 0 0 0 0 0 0 - - "complex128" 0 0 1 p2:18:14:0:0
var 0 0 "c" 5 1 0 0 0 8 y24 "./cplx0.go" 18 14 0 0 1 0 v0
scope 0 0 - 0
dieref y19 2 y22 0
dieoff y22 0:17
data y19 SDWARFFCN 19 0 0 06000000000060019c29000000000000000000 4
reloc 1 4 R_DWARFSECREF 0 y22
reloc 5 1 R_DWTXTADDR_U1 0 y1
reloc 10 4 R_DWARFSECREF 0 y22
reloc 14 4 R_DWARFSECREF 0 y20
data y20 SDWARFLOC 27 0 0 010004002408904093089041930804246008910893089110930800 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y21 SDWARFRANGE 0 0 0 - 0
data y23 SDWARFLINES 31 0 0 00090200000000000000000402030c140a8706af0637063706d70228000101 1
reloc 3 8 R_ADDR 0 y1
data y22 SDWARFABSFCN 26 0 1 056d61696e2e646f7072696e7400011201226300000000000000 1
reloc 21 4 R_DWARFSECREF 0 y24
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`) with P0' (`p0PrimeSyms`, as `gen-check`
runs G56 to G63). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) := do
  let (lc, ps, bs, g) ← GenG2.load fSsa fProg
  let (syms', ps') ← GoFV.Asm.p0PrimeSyms g.syms ps
  return (lc, ps', bs, { g with syms := syms' })

/-- `runLoc`'s context of `doprint`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G63's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG63` gives. -/
def tab : PcTab := (match checkG63 lc0 ps bs g with
  | .ok (t, _) => t
  | .error _ => [])

/-- The class table `checkG63` gives. -/
def kt : KTab := (match checkG63 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

/-- `b1`, the entry, whose value 2 is `v2 = StoreReg v15`. -/
def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0''s layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame with 8 bytes of extra
space, every symbol at `symA`; `NAME_PARAM` 0 is `SP + 24`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, the home slots at their frame operands and the PC table of `checkG63`; not G48's mode
(`outSP = false`). -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := GenG2.sp0,
    slot := fun k =>
      if k ∈ homeSlots lc then (g.slotOp k).map (fun p => frameOff L p.1 p.2) else none,
    g := 0x9000, lr := 0, fp := 0, framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The bits of the `float64` `1.5`. -/
def X : BitVec 64 := 0x3FF8000000000000

/-- A state before `v2`: `1.5` in `F0` (Go register 31, `v15`'s home), every other register
`poison`, no slot, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 9 none, args := [], mem0 := GenG2.mem0, images := #[] },
    regs := Array.ofFn (n := 64) fun i => if i.val = 31 then .int .w64 X else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v2`: the activation's `g` and `FP`, the PC of `v2`, `1.5` in the low bits
of `V0`, the memory 0. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun k => if k = 0 then X.setWidth 128 else 0,
    nzcv := ⟨false, false, false, false⟩, pc := E.pcOf 1 2, mem := fun _ => 0 }

/-- The home slots lie above the saved `LR` and below `2^64`. -/
def slotsFit : Bool :=
  (homeSlots lc).all fun k =>
    match g.slotOp k with
    | some (nc, off) => decide (8 ≤ frameOff L nc off) &&
        decide (GenG2.sp0.toNat + (frameOff L nc off).toNat + 8 ≤ 2 ^ 64)
    | none => true

/-- A home `h` that is a slot at `SP + 24` (`slot`) of 8 bytes (`size`). Generic in its inputs, so
that its spec never makes the kernel evaluate the function. -/
def slotAt (h : Option Location) (slot : SlotKey → Option Int) (size : SlotKey → Nat) : Bool :=
  match h with
  | some (.slot k) => slot k == some 24 && size k == 8
  | _ => false

theorem slotAt_spec {h : Option Location} {slot : SlotKey → Option Int} {size : SlotKey → Nat}
    (H : slotAt h slot size = true) : ∃ k, h = some (.slot k) ∧ slot k = some 24 ∧ size k = 8 := by
  unfold slotAt at H
  split at H
  · rename_i k
    simp only [Bool.and_eq_true, beq_iff_eq] at H
    exact ⟨k, rfl, H.1, H.2⟩
  · cases H

/-- After `v2`: the slot of `c`'s first piece (home `h`) holds `X`. -/
def holdsX (h : Option Location) (s : LocState) : Bool :=
  match h with
  | some (.slot k) =>
    match s.slots.lookup k with
    | some (.int .w64 n) => n == X
    | _ => false
  | _ => false

theorem holdsX_spec {h : Option Location} {s : LocState} (H : holdsX h s = true) :
    ∃ k, h = some (.slot k) ∧ s.slots.lookup k = some (.int .w64 X) := by
  unfold holdsX at H
  split at H
  · rename_i k
    split at H
    · rename_i n hn
      simp only [beq_iff_eq] at H
      subst H
      exact ⟨k, rfl, hn⟩
    · cases H
  · cases H

/-- What compiled evaluation checks on `doprint`: it holds an arm64 op; on P0', `checkG63` accepts
it with `tab` and `kt` and `checkG62` does not (G62 spills X registers only); it accesses no frame
variable, its home slots fit and it needs no G48 mode; G2's symbols have no float constant; `b1`
holds `v2` (`StoreReg v15`) at index 2, where G35's table is empty and the class table gives `F0`
class 64; `v2`'s home is a slot at `SP + 24` of 8 bytes; `stepLoc` runs `v2` from `s0` to that
slot holding `X`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG63 lc0 ps bs g).toOption == some (tab, kt) && (checkG62 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && slotsFit && needs48 lc == false &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 2).isSome && blk.values[2]? == some 2 &&
    (val 2).op == .StoreReg && (val 2).id == 2 &&
    (constRo (symNames g)).isEmpty &&
    uL35 lc (uIn35 lc 1) blk 2 == [] && (kAt lc kt 1 blk 2).get 31 == some 64 &&
    slotAt (lc.home 2) E.slot (fun k => (E.lc.slotTy k).size) &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 2)) (holdsX (lc.home 2))

theorem g63_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG63 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG62 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ slotsFit = true ∧ needs48 lc = false ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 2 = some (val 2) ∧ blk.values[2]? = some 2 ∧
      (val 2).op = .StoreReg ∧ (val 2).id = 2 ∧
      (constRo (symNames g)).isEmpty = true ∧
      uL35 lc (uIn35 lc 1) blk 2 = [] ∧ (kAt lc kt 1 blk 2).get 31 = some 64 ∧
      slotAt (lc.home 2) E.slot (fun k => (E.lc.slotTy k).size) = true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 2)) (holdsX (lc.home 2)) = true := by
  have hf := g63_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h62, hav, hfit, h48, hm1, hbs, hvs, hi2, hop, hid, hro, hu0, hk31, hat,
    hrun⟩ := hf
  refine ⟨hl, ?_, h62, hav, hfit, h48, hm1, ?_, ?_, hi2, hop, hid, hro, hu0, hk31, hat, hrun⟩
  · revert hres; cases checkG63 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g63Env (hc : checkG63 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
                checkG63L_spec hl (checkG63_spec hc).2
              intro p hp
              exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := GenG2.addrAgree
            glob := fun _ _ _ _ => rfl
            syms := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -, -, -⟩ :=
                checkG63L_spec hl (checkG63_spec hc).2
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
    (r = 31 ∧ x = .int .w64 X) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h31
      exact .inl ⟨h31, h.symm⟩
    · exact .inr h.symm
  · cases h

/-- `F0` is Go register 31, the obj register `V0`. -/
theorem objV31 : objV? 31 = some (BitVec.ofNat 5 0) := by decide

theorem locMatch0 : LocMatch E s0 1 2 m0 where
  regs := by
    intro r x hx
    rcases s0_regs hx with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rw [objX?_none_of_V objV31] at hk
        cases hk
      · rw [objV31] at hk
        cases hk
        show ((m0.v (BitVec.ofNat 5 0)).setWidth 64 : BitVec 64) = X
        decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl,
    by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g63Inv0 (hk31 : (kAt lc kt 1 blk 2).get 31 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk 2) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, GenG2.keys0, GenG2.sep0⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [hk31] at hc
      cases hc
      show kNarrow 64 64 = true
      decide
    · trivial
  slots := by intro k v h; simp [s0] at h

/-! ## `v2`: `StoreReg v15` (`FMOVD F0, c+0(FP)`) -/

/-- The per-value premises of G54 on `v2`, `StoreReg`: none of them applies. -/
theorem pre54 (hop : (val 2).op = .StoreReg) : G54Pre lc s0 (val 2) := by
  have hne : ∀ o : Op, o ≠ .StoreReg → (val 2).op ≠ o := fun o h h' => h (h'.symm.trans hop)
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

/-- **G63 on `doprint` of `test/ken_cplx0`** (`v2 = StoreReg v15`, the float spill
`FMOVD F0, c+0(FP)`): `checkG62` rejects the function and `checkG63` accepts it. From a state with
`1.5` in `F0`, `stepLoc` runs `v2` to the slot of `c`'s first piece holding its bits `X`, and
`g63_value` (at the mode `false`, the function needing no G48 mode) relates it to a machine run
from `m0`, which holds `X` in `V0`, to a state whose word at `SP + 24`, the slot, is `X`, under an
activation extending `E` that is again a `G49Env`. -/
theorem genG63_witness :
    (checkG62 lc0 ps bs g).toOption = none ∧
      ∃ s1 E1 m1 k, stepLoc GenG2.env lc s0 (val 2) = .ok s1 ∧ lc.home 2 = some (.slot k) ∧
        s1.slots.lookup k = some (.int .w64 X) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 3 m1 ∧
        (readMem m1.mem (GenG2.sp0 + BitVec.ofInt 64 24) 8).setWidth 64 = X := by
  obtain ⟨hl, hc, h62, hav, hfit, h48, hm1, hb, hv2, hi2, hop, hid, hro, hu0, hk31, hat, hrun⟩ :=
    facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  obtain ⟨k, hk, hlook⟩ := holdsX_spec hr
  have hE := g63Env hc hl hav hfit
  have hne : ∀ o : Op, o ≠ .StoreReg → (val 2).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  -- `g63_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 2 = some (val 2) := by
    rw [← liveCtx_ctx (lc := lc0)]; exact hv2
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -, -⟩ := g63_value (H := GenG2.H0) (env := GenG2.env)
    (osp := false) hc hE hl0 hm0 hb0 hi2 hv0 (by rw [hop]; rfl) locMatch0 (g63Inv0 hk31)
    (fun h => by cases h) (fun h => by cases h)
    (fun h => by
      have h' : needs48 lc = true := h
      rw [h48] at h'
      cases h')
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 2); rw [hu0]; intro e he; cases he)
    (pre54 hop) (ro0 hro)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide)))
    (fun h => by cases h) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  refine ⟨h62, s1, E1, m1, k, hs1, hk, hlook, hx1, hE1, hp1, hm1', ?_⟩
  obtain ⟨o, ho, hrel⟩ := hm1'.slots k _ hlook
  obtain ⟨hEq, -⟩ := hx1
  have hslot : E1.slot = E.slot := by rw [hEq]
  have hsp : E1.sp = E.sp := by rw [hEq]
  have hlc : E1.lc = E.lc := by rw [hEq]
  obtain ⟨k', hh', h24, h8⟩ := slotAt_spec hat
  rw [hk] at hh'
  cases hh'
  rw [hslot, h24] at ho
  cases ho
  unfold SlotRel at hrel
  rw [hlc, h8, hsp] at hrel
  exact valRel_i64 hE1.env.env.env.env.env.addr hrel

end GoFV.Proof.Witness.GenG63
