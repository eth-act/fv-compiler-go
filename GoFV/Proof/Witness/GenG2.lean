import GoFV.Proof.Gen.G2
import GoFV.Proof.Witness.GenG1

/-!
# Non-vacuity witness: slice G2 of the genssa validator on `testInts` and `clamp`

`test/makeslice/main/testInts,1.ssa` and `test/makeslice/main/testInts,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`testIntsSsa`, `testIntsProg`):

```go
func testInts(n uint64) {
	testMakeInts(n)
	testMakeCopyInts(n)
	testMakeInAppendInts(n)
}
```

`load` parses both files, runs `Env.load` and `genssa` on the exported frame and builds `checkG2`'s
input `G2In` (the Prog list's symbols and the slots' frame operands) as `gen-check` does. By
compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`, as
`verifiedPipeline_witness`; `g2_facts`), `checkG2` accepts `testInts` with the PC table `tab`, and
from the state after the entry value `v5` (`n = 7` in `R0`), `stepLoc` runs the spill `v2`
(`StoreReg` to `n`'s parameter slot), the static call `v6` (`CALL main.testMakeInts(SB)`, no
results), its memory `v7` (`SelectN`) and the reload `v3` (`LoadReg`); the entry value `v1`
(`InitMem`, no code) between `v2` and `v6` is not run. On a framed activation with `G2Env`
(`SP = 0x7fff0000`, the slot at `SP + 40` with `autosize = 32`, `extrasize = 8`, every symbol at
`2^40`, `ι` the nil block and the globals there, the Progs at `0x10000 + 4·ID`, `ret = 0`) and the
callee contract of a callee that returns at once with the memory unchanged (`H0` returns to
`X30`; `env` returns no results and the memory), `g2_value` four times gives a machine run of the
Progs (`MOVD R0, n(FP)`; `CALL`, the hook; `MOVD n(FP), R0`) to a state related by `LocMatch`
before `v4` (`genG2_value_witness`).

`g2_term` (and `g2_value` on a G1 value) on `clamp` (`GoFV/Proof/Witness/GenG1.lean`):
`checkG2` accepts it with G1's table; on a frameless activation with `G2Env`, `g2_value` runs the
compare `v7` and `g2_term` the `GT` block `b1` (`genG2_term_witness_50`, `genG2_term_witness_30`).
-/

namespace GoFV.Proof.Witness.GenG2

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/makeslice/main/testInts,1.ssa` (quick-v10). -/
def testIntsSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "testInts" 1 0 0
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
type t2 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t1 FUNC 8 8 8 hasptr,direct "func(uint64)" "func(uint64)" 0 1 0
field 0 "n" t2 ? 0
aux a2 sym "main.testInts" "main.testInts" 1 - 0 - - - - 0
posbase p2 "./makeslice.go" 1 1 -1
aux a3 name "n" "n" PPARAM t2 0 1 used p2:53:15:0:0
aux a1 call "AuxCall{main.testInts}" a2 1 1 0 8 8 1 0
abiparam in 0 t2 a3 0 0
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t4 INT8 1 1 0 comparable,named "int8" "int8"
type t5 INT16 2 2 0 comparable,named "int16" "int16"
type t6 INT32 4 4 0 comparable,named "int32" "int32"
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
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
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
aux a5 sym "main.testMakeInts" "main.testMakeInts" 1 - 0 - - - - 0
aux a4 call "AuxCall{main.testMakeInts}" a5 1 1 0 8 8 1 0
abiparam in 0 t2 - 0 0
aux a7 sym "main.testMakeCopyInts" "main.testMakeCopyInts" 1 - 0 - - - - 0
aux a6 call "AuxCall{main.testMakeCopyInts}" a7 1 1 0 8 8 1 0
abiparam in 0 t2 - 0 0
aux a9 sym "main.testMakeInAppendInts" "main.testMakeInAppendInts" 1 - 0 - - - - 0
aux a8 call "AuxCall{main.testMakeInAppendInts}" a9 1 1 0 8 8 1 0
abiparam in 0 t2 - 0 0
slot s1 a3 t2 0 - 0
f b1 t1 a1 12 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t2,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:0:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:0:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:0:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:0:0 1 v11
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
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 3 "early deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 4 "short circuit"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 5 "decompose user"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 7 "opt"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 8 "zero arg cse"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 9 "opt deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 10 "generic cse"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
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
cache linestarts 2:54:57
dcllen 1
end
pass 11 "phiopt"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
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
cache linestarts 2:54:57
dcllen 1
end
pass 12 "gcse deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
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
cache linestarts 2:54:57
dcllen 1
end
pass 13 "nilcheckelim"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
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
cache linestarts 2:54:57
dcllen 1
end
pass 14 "prove"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
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
cache linestarts 2:54:57
dcllen 1
end
pass 15 "divisible"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
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
cache linestarts 2:54:57
dcllen 1
end
pass 16 "divmod"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
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
cache linestarts 2:54:57
dcllen 1
end
pass 17 "middle opt"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
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
cache linestarts 2:54:57
dcllen 1
end
pass 18 "known bits"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
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
cache linestarts 2:54:57
dcllen 1
end
pass 19 "early fuse"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 3 -
v v6 StaticLECall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticLECall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticLECall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
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
cache linestarts 2:54:57
dcllen 1
end
pass 20 "expand calls"
aux a10 nameoff "n+0" a3 0
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
v v4 SB t15 0 - p0:0:0:0:0 0 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v2 OffPtr t33 0 - p0:0:0:0:0 0 v3
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
cache linestarts 2:54:57
dcllen 1
end
pass 21 "decompose builtin"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
v v4 SB t15 0 - p0:0:0:0:0 0 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v2 OffPtr t33 0 - p0:0:0:0:0 0 v3
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
cache linestarts 2:54:57
dcllen 1
end
pass 22 "softfloat"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
v v4 SB t15 0 - p0:0:0:0:0 0 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v2 OffPtr t33 0 - p0:0:0:0:0 0 v3
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
cache linestarts 2:54:57
dcllen 1
end
pass 23 "branchelim"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
v v4 SB t15 0 - p0:0:0:0:0 0 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v2 OffPtr t33 0 - p0:0:0:0:0 0 v3
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
cache linestarts 2:54:57
dcllen 1
end
pass 24 "late opt"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 25 "dead auto elim"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 26 "sccp"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 27 "generic deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 28 "late fuse"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 29 "check bce"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 30 "dse"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 31 "memcombine"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 32 "writebarrier"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 StaticCall t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 StaticCall t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 StaticCall t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 33 "lower"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 34 "addressing modes"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 35 "late lower"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 36 "pair"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 2:54:57
dcllen 1
end
pass 38 "lowered cse"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
dcllen 1
end
pass 39 "elim unread autos"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
dcllen 1
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
dcllen 1
end
pass 41 "lowered deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
dcllen 1
end
pass 42 "checkLower"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
dcllen 1
end
pass 43 "loop invariant"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
dcllen 1
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
dcllen 1
end
pass 45 "tighten"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
dcllen 1
end
pass 46 "late deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
dcllen 1
end
pass 47 "critical"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
dcllen 1
end
pass 48 "phi tighten"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
dcllen 1
end
pass 49 "likelyadjust"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
dcllen 1
end
pass 50 "layout"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
fstate laidout
dcllen 1
end
pass 51 "schedule"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
fstate scheduled,laidout
dcllen 1
end
pass 52 "late nilcheck"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
fstate scheduled,laidout
dcllen 1
end
pass 53 "flagalloc"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 3 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v5,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v5,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
fstate scheduled,laidout
dcllen 1
end
pass 54 "regalloc"
aux a4 call "AuxCall{main.testMakeInts}" a5 1 1 0 8 8 1 0
abiparam in 0 t2 - 0 0
callreg 0:1 - 7fffffff97ffffff -
aux a6 call "AuxCall{main.testMakeCopyInts}" a7 1 1 0 8 8 1 0
abiparam in 0 t2 - 0 0
callreg 0:1 - 7fffffff97ffffff -
aux a8 call "AuxCall{main.testMakeInAppendInts}" a9 1 1 0 8 8 1 0
abiparam in 0 t2 - 0 0
callreg 0:1 - 7fffffff97ffffff -
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 2 -
v v2 StoreReg t2 0 - p2:57:1:0:0 2 v5
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v3 LoadReg t2 0 - p2:55:18:2:0 1 v2
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v3,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v4 LoadReg t2 0 - p2:56:22:2:0 1 v2
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v4,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
fstate scheduled,laidout
regalloc 11 v2:@a3/t2/0/-/0,v3:R0,v4:R0,v5:R0,v6:[],v8:[],v10:[]
dcllen 1
end
pass 55 "loop rotate"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 2 -
v v2 StoreReg t2 0 - p2:57:1:0:0 2 v5
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v3 LoadReg t2 0 - p2:55:18:2:0 1 v2
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v3,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v4 LoadReg t2 0 - p2:56:22:2:0 1 v2
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v4,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
fstate scheduled,laidout
regalloc 11 v2:@a3/t2/0/-/0,v3:R0,v4:R0,v5:R0,v6:[],v8:[],v10:[]
dcllen 1
end
pass 56 "trim"
f b1 t1 a1 12 1
b b1 Ret p2:57:1:0:0 0 0 - v12 - -
v v5 ArgIntReg t2 0 a10 p2:57:1:0:0 2 -
v v2 StoreReg t2 0 - p2:57:1:0:0 2 v5
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p2:54:14:1:0 1 v5,v1
v v7 SelectN t28 0 - p2:54:14:0:0 1 v6
v v3 LoadReg t2 0 - p2:55:18:2:0 1 v2
v v8 ARM64CALLstatic t32 8 a6 p2:55:18:1:0 1 v3,v7
v v9 SelectN t28 0 - p2:55:18:0:0 1 v8
v v4 LoadReg t2 0 - p2:56:22:2:0 1 v2
v v10 ARM64CALLstatic t32 8 a8 p2:56:22:1:0 1 v4,v9
v v11 SelectN t28 0 - p2:56:22:0:0 1 v10
v v12 MakeResult t32 0 - p2:57:1:1:0 1 v11
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a10:2
cache linestarts 2:54:57
fstate scheduled,laidout
regalloc 11 v2:@a3/t2/0/-/0,v3:R0,v4:R0,v5:R0,v6:[],v8:[],v10:[]
dcllen 1
end
frontend
end
ptrcache t5,t6,t7,t8,t10,t11,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t2,t11,t14,t15,t25,t26,t12,t13,t3,t17,t18,t19,t33,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32
eof
"#

/-- `test/makeslice/main/testInts,1.prog` (quick-v10). -/
def testIntsProg : String := r#"gofv-prog 3
pkg "main"
func "testInts" 1
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
name n1 "n" PPARAM t1 1 "main.n" 0 a3
in n1 0 used
out n1 0 used
stack 0 0 8
end
genin
posbase p2 "./makeslice.go" 1 1 -1 1 "./makeslice.go" "./makeslice.go" 1 1
sym y1 "main.testInts" 1
curfn p2:53:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 53 200080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "main.testInts.arginfo1" 0
sym y4 "main.testInts.argliveinfo" 0
sym y5 "main.n" 0
sym y6 "main.testMakeInts" 1
sym y7 "main.testMakeCopyInts" 1
sym y8 "main.testMakeInAppendInts" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p2:53:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:53:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:53:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:53:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:53:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:53:6:2:0
p 6 6 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/PARAM/0/0/y5/- 0 0 p2:57:1:2:0
p 7 7 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:57:1:2:0
p 8 8 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p2:54:14:1:0
p 9 9 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p2:54:14:1:0
p 10 10 0 0 0 - MOVD 0 MEM/8383/0/0/PARAM/0/0/y5/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:55:18:1:0
p 11 11 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p2:55:18:1:0
p 12 12 0 0 0 - MOVD 0 MEM/8383/0/0/PARAM/0/0/y5/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:56:22:1:0
p 13 13 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y8/- 0 0 p2:56:22:1:0
p 14 14 0 0 0 - RET 0 _ 0 - _ 0 0 p2:57:1:0:0
p 15 15 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 53 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:1:6:50,1:6:-1:-30000:9108
dbgregout -
dbgpc 1:6:10
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i8 0 0 p2:53:6:0:0
p 16 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:53:6:0:0
p 17 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:53:6:0:0
p 18 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:53:6:0:0
p 19 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@28 0 0 p2:53:6:0:0
p 20 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:53:6:0:0
p 21 12 32 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-32/-/- 0 0 p2:53:6:0:1
p 22 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:53:6:0:0
p 23 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:53:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:53:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:53:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:53:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:53:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:53:6:2:0
p 6 24 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/0/y5/- 0 0 p2:57:1:2:0
p 7 28 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:57:1:2:0
p 8 28 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p2:54:14:1:0
p 9 28 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y6/- 0 0 p2:54:14:1:0
p 10 32 0 0 329 - MOVD 0 MEM/0/0/0/PARAM/48/0/y5/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:55:18:1:0
p 11 36 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y7/- 0 0 p2:55:18:1:0
p 12 40 0 0 329 - MOVD 0 MEM/0/0/0/PARAM/48/0/y5/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:56:22:1:0
p 13 44 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y8/- 0 0 p2:56:22:1:0
p 14 48 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:57:1:0:0
p 24 52 -32 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/32/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:57:1:0:0
p 25 56 32 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:57:1:0:0
p 26 60 -32 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:57:1:0:0
p 27 60 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:53:6:0:0
p 28 60 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:53:6:0:0
p 29 60 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p2:53:6:0:0
p 30 64 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:53:6:0:0
p 31 68 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y9/- 0 0 p2:53:6:0:0
p 32 72 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:53:6:0:0
p 33 72 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:53:6:0:0
p 34 76 32 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@16 0 0 p2:53:6:0:0
fn y1 8 24 0 0 53 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 80 0 900b40f9ff6330eba9010054fe0f1ef8fd831ff8fd2300d1e01700f900000094e01740f900000094e01740f900000094fd835ff8fe0742f8c0035fd6e00700f9e3031eaa00000094e00740f9edffff17 4
reloc 28 4 R_CALLARM64 0 y6
reloc 36 4 R_CALLARM64 0 y7
reloc 44 4 R_CALLARM64 0 y8
reloc 68 4 R_CALLARM64 0 y9
pcln y14 y15 y16 y17 y10,y11,y12,y13 y2,y2,_,_,_,y3,y4
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y10 SRODATA 11 1 28000 00010102020c0103020200 0
data y11 SRODATA 7 1 28000 00070208010500 0
data y12 SRODATA 0 1 28000 - 0
data y13 SRODATA 7 1 28000 00060401030d00 0
data y14 SRODATA 7 1 28000 0204400a3f0600 0
data y15 SRODATA 3 1 28000 041400 0
data y16 SRODATA 15 1 28000 6c0608010501020202020203070500 0
data y17 SRODATA 3 1 28000 001400 0
end
dwarf
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
sym y21 "" 0
sym y22 "go:info.uint64" 0
dwfn y18 y19 y20 - y21 "main.testInts" 1:53 1 0 1 61
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwname n1 1 1 0 0 0 0 0 0 - - "uint64" 0 0 1 p2:53:15:0:0
var 0 0 "n" 5 1 0 0 0 8 y22 "./makeslice.go" 53 15 0 0 0 0 v0
scope 0 0 - 0
data y18 SDWARFFCN 39 0 0 036d61696e2e74657374496e7473000050019c0200000035012d6e000035000000000000000000 3
reloc 15 1 R_DWTXTADDR_U1 0 y1
reloc 30 4 R_DWARFSECREF 0 y22
reloc 34 4 R_DWARFSECREF 0 y19
data y19 SDWARFLOC 14 0 0 0100040020015004205002910800 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y20 SDWARFRANGE 0 0 0 - 0
data y21 SDWARFLINES 31 0 0 00090200000000000000000402032f140a87068b0634386060830214000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- Go's frame layout of slot `k`: the name class and operand offset (`gen-check`'s `slotOpOf`). -/
def slotOpOf (env : GoFV.Gen.Env) (offs : Array (Option Int)) (k : SlotKey) :
    Option (GoFV.Asm.AddrName × Int) := do
  let n ← env.nameOfAux? k.name
  let off ← (offs[n]?).join
  let x ← (env.name n).toOption
  let outregs := (env.inFlags[n]?).any (·.outregs)
  let cls := if x.cls == "PPARAM" || (x.cls == "PPARAMOUT" && !outregs) then GoFV.Asm.AddrName.PARAM
    else .AUTO
  return (cls, off + k.off)

/-- `runLoc`'s context of the function after `trim`, genssa's P0 Progs in list order, the Prog ID
of each block's start and `checkG2`'s input (as `gen-check`). -/
def load (ssa prog : String) :
    Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) := do
  let (e, _) ← GoFV.SSA.parseExportExt ssa.toUTF8
  let pf ← GoFV.Asm.parseProgFile prog.toUTF8
  let env ← GoFV.Gen.Env.load e pf
  let fr : GoFV.Gen.FrameOut :=
    { dcl := pf.frame.dclOut, optDcl := pf.frame.optDcl, merges := pf.frame.merges,
      stksize := pf.frame.stksize, stkptrsize := pf.frame.stkptrsize,
      stkalign := pf.frame.stkalign }
  let out ← GoFV.Gen.genssa env fr
  return (LocCtx.make env.tabs env.f, out.order.filterMap (out.st.progs[·]?),
    fun b => (out.st.bstart[b]?).join,
    { syms := out.st.syms, slotOp := slotOpOf env (GoFV.Gen.Ctx.ofFrame env fr).offsets,
      stksize := fr.stksize })

/-- The loaded `testInts`. -/
def tiIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  load testIntsSsa testIntsProg

def lc : LocCtx :=
  match tiIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

def ps : Array GoFV.Asm.Prog :=
  match tiIn with
  | .ok x => x.2.1
  | .error _ => #[]

def bs : ID → Option Nat :=
  match tiIn with
  | .ok x => x.2.2.1
  | .error _ => fun _ => none

def g : G2In :=
  match tiIn with
  | .ok x => x.2.2.2
  | .error _ => { syms := #[], slotOp := fun _ => none, stksize := 0 }

/-- The PC table `checkG2` gives (block `b1`: the index of each value's first Prog and of the
terminator's). -/
def tab : PcTab := [(1, [5, 5, 7, 7, 10, 10, 11, 12, 12, 13, 14, 14, 14])]

/-- Block `b1`: `v5 = ArgIntReg`, `v2 = StoreReg v5`, `v1 = InitMem`, `v6 = CALLstatic v5 v1`,
`v7 = SelectN [0] v6`, `v3 = LoadReg v2`, …; `Ret`. -/
def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- The text base of the layout. -/
def text : BitVec 64 := 0x10000

/-- Where every symbol (callee or global) is linked: above the Progs. -/
def symA : BitVec 64 := 0x10000000000

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 32-byte frame with 8 bytes of extra
space, every symbol at `symA`. -/
def L : Link := Link.byId (fun _ => symA) text 32 8 ps.toList

/-- `ι`: the nil block, and the globals at their symbols. -/
def ι : Blk → Option (BitVec 64)
  | .nil => some 0
  | .global _ => some symA
  | _ => none

def sp0 : BitVec 64 := 0x7fff0000

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the home
slots at their frame operands and the PC table of `checkG2`. -/
def E : MatchEnv :=
  { lc, ι, sp := sp0,
    slot := fun k => if k ∈ homeSlots lc then (g.slotOp k).map (fun p => frameOff L p.1 p.2) else none,
    g := 0x9000, lr := 0, fp := 0, framed := true, pcOf := pcOfTab text ps.toList tab }

/-- The empty memory. -/
def mem0 : Mem := {}

/-- The `runLoc` state after the entry value `v5`: `n` in `R0`, every other register `poison`. -/
def s0 (x : BitVec 64) : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .i64 x else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v2`: `X0 = n`, the activation's `g` and `FP`, the PC of `v2`. -/
def m0 (x : BitVec 64) : MState :=
  { x := fun k => if k = 0 then x else if k = 28 then 0x9000 else if k = 29 then sp0 - 8 else 0,
    sp := sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 1, mem := fun _ => 0 }

/-- A callee that returns at once: to `X30`. -/
def H0 : Hooks := ⟨fun m => some (.ret { m with pc := m.x 30 })⟩

/-- Every callee returns no results and the memory unchanged. -/
def env : Env := { extern := fun _ => some fun _ _ m => .returned [] m }

/-- The memory is `mem0`. -/
def memIs0 : Val → Bool
  | .mem mm => decide (mm = mem0)
  | _ => false

/-- The static call `v` has no results. -/
def noOuts (v : Value) : Bool :=
  match callOf? lc.ctx.tabs v.aux with
  | some (_, _, cabi) =>
    match callRegs cabi with
    | .ok (_, outs) => outs.isEmpty
    | .error _ => true
  | none => true

/-- The home slots lie above the saved `LR` and below `2^64`. -/
def slotsFit : Bool :=
  (homeSlots lc).all fun k =>
    match g.slotOp k with
    | some (nc, off) => decide (8 ≤ frameOff L nc off) &&
        decide (sp0.toNat + (frameOff L nc off).toNat + 8 ≤ 2 ^ 64)
    | none => true

/-- What compiled evaluation checks on `testInts`: `checkG2` accepts it with `tab`; `b1` holds
`v2`, `v6`, `v7`, `v3` at 1, 3, 4, 5; their ops; `v6` has no results; the slots fit; `R0` holds
64-bit values; and `stepLoc` runs `v2`, `v6` (to the memory `mem0`), `v7`, `v3`. -/
def tiFacts (x : BitVec 64) : Bool :=
  (checkG2 lc ps bs g).toOption == some tab && lc.ctx.f.blocks.toList.contains 1 &&
    (lc.ctx.f.block? 1).isSome && (lc.ctx.f.value? 2).isSome && (lc.ctx.f.value? 6).isSome &&
    (lc.ctx.f.value? 7).isSome && (lc.ctx.f.value? 3).isSome &&
    blk1.values[1]? == some 2 && blk1.values[3]? == some 6 && blk1.values[4]? == some 7 &&
    blk1.values[5]? == some 3 &&
    (val 2).op == .StoreReg && (val 6).op == .ARM64CALLstatic && (val 7).op == .SelectN &&
    (val 3).op == .LoadReg && noOuts (val 6) && slotsFit && regCls lc 0 == some 64 &&
    GenG1.okThen (stepLoc env lc (s0 x) (val 2)) fun s1 =>
      GenG1.okThen (stepLoc env lc s1 (val 6)) fun s2 => memIs0 s2.mem &&
        GenG1.okThen (stepLoc env lc s2 (val 7)) fun s3 =>
          GenG1.okThen (stepLoc env lc s3 (val 3)) fun _ => true

/-- `testInts` from the state after `v5` with `n = 7`. -/
theorem g2_facts : tiFacts 7 = true := by
  native_decide

theorem addrAgree : AddrAgree ι := by
  intro b n a hb ha
  cases b <;> simp [ι] at ha <;> simp [Blk.base?] at hb
  subst hb; subst ha; rfl

theorem memInj0 {ι' : Blk → Option (BitVec 64)} (h : ι' .nil = some 0) (mm : Memory) :
    MemInj ι' mem0 mm where
  nil := h
  mapped := by intro b al h; simp [mem0] at h
  inj := by intro b al b' al' a a' h; simp [mem0] at h
  bytes := ⟨fun _ _ => False, by intro b al a h; simp [mem0] at h⟩

theorem keys0 : KeysNodup mem0 := by simp [KeysNodup, mem0]

theorem sep0 {ι' : Blk → Option (BitVec 64)} {P : BitVec 64 → Prop} : SepFrom ι' P mem0 := by
  intro b al a h; simp [mem0] at h

theorem prog_addr_ne {p : GoFV.Asm.Prog} (hid : p.id < 2 ^ 32) (hp : p ∈ ps.toList) {a : BitVec 64}
    (ha : a.toNat < 0x10000 ∨ 0x10000 + 4 * 2 ^ 32 ≤ a.toNat) (ha' : a.toNat < 2 ^ 64) :
    L.addr p.id ≠ some a := by
  intro h
  rw [L, addr_byId hp] at h
  have := congrArg BitVec.toNat (Option.some.inj h)
  simp [text, BitVec.toNat_add] at this
  omega

theorem g2Env (hc : checkG2 lc ps bs g = .ok tab) : G2Env lc g L ps 0 tab E where
  lcEq := rfl
  link := rfl
  pcOf := rfl
  retOut := by
    obtain ⟨-, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG2_spec hc
    intro p hp
    exact prog_addr_ne (hlt p hp) hp (by simp) (by simp)
  addr := addrAgree
  glob := fun _ _ _ _ => rfl
  syms := by
    obtain ⟨-, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG2_spec hc
    intro y
    have hs : L.sym y = symA := rfl
    rw [hs]
    refine ⟨by decide, fun p hp => ?_⟩
    exact prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
  calls := fun h => by cases h
  slot := fun k hk nc off hs => by simp [E, hk, hs]
  extra := by decide
  frame := by
    refine ⟨by decide, by decide, fun k off hk => ?_⟩
    have hf := g2_facts
    simp only [tiFacts, Bool.and_eq_true] at hf
    have hfit := hf.1.1.2
    simp only [E] at hk
    split at hk
    · rename_i hmem
      obtain ⟨⟨nc, o⟩, hso, rfl⟩ := Option.map_eq_some_iff.1 hk
      have := List.all_eq_true.1 hfit k hmem
      simp only [hso, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this
    · cases hk

theorem locMatch0 (x : BitVec 64) : LocMatch E (s0 x) 1 1 (m0 x) where
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
          exact Or.inl rfl
        · subst hv; trivial
      · split at hv
        · rename_i h0; subst h0; simp [objV?] at hk
        · subst hv; trivial
    · cases hv
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem0, rfl, memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g2Inv0 (x : BitVec 64) (h0 : regCls lc 0 = some 64) : G2Inv E lc (s0 x) where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, keys0, sep0⟩
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

/-- The callee contract of a callee that returns at once with the memory `mem0` and no
results. -/
theorem callOK0 {E' : MatchEnv} (hA : AddrAgree E'.ι) (hnil : E'.ι .nil = some 0)
    {s s' : LocState} {v : Value} {m : MState} (hmem : memIs0 s'.mem = true)
    (hno : noOuts v = true) : CallOK H0 E' g L lc s s' v m := by
  intro _ name abi cabi ins outs y args mm m₁ hc hcr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hout : outs = [] := by
    simp only [noOuts, hc, hcr, List.isEmpty_iff] at hno
    exact hno
  have hm' : s'.mem = .mem mem0 := by
    unfold memIs0 at hmem
    split at hmem
    · rename_i mm' he
      rw [he, of_decide_eq_true hmem]
    · cases hmem
  subst hout
  exact ⟨E'.ι, { m₁ with pc := m₁.x 30 }, mem0, rfl, fun _ _ h => h, hA, rfl, rfl, rfl, rfl,
    fun _ _ => rfl, hm', memInj0 hnil _, keys0, sep0, fun r hr => by cases hr⟩

/-- An op other than a static call: `CallOK` holds vacuously. -/
theorem callOK_ne {E' : MatchEnv} {s s' : LocState} {v : Value} {m : MState}
    (h : v.op ≠ .ARM64CALLstatic) : CallOK H0 E' g L lc s s' v m := fun hop => absurd hop h

/-- **G2 on `testInts`**: from the state after `v5`, the spill `v2`, the call `v6`, its memory
`v7` and the reload `v3` are matched by a machine run of the Progs to a state related before
`v4`, under an activation that extends `E`. -/
theorem genG2_value_witness :
    ∃ s1 s2 s3 s4 E' m4, stepLoc env lc (s0 7) (val 2) = .ok s1 ∧
      stepLoc env lc s1 (val 6) = .ok s2 ∧ stepLoc env lc s2 (val 7) = .ok s3 ∧
      stepLoc env lc s3 (val 3) = .ok s4 ∧ E.Extends E' ∧ G2Env lc g L ps 0 tab E' ∧
      PStar H0 L ps.toList 0 (m0 7) m4 ∧ LocMatch E' s4 1 6 m4 := by
  have hf := g2_facts
  simp only [tiFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, hmem⟩, hbs⟩, hv2s⟩, hv6s⟩, hv7s⟩, hv3s⟩, hi1⟩, hi3⟩, hi4⟩, hi5⟩,
    hop2⟩, hop6⟩, hop7⟩, hop3⟩, hno⟩, -⟩, hcls⟩, hrun⟩ := hf
  have hc : checkG2 lc ps bs g = .ok tab := by
    revert hck; cases checkG2 lc ps bs g <;> simp [Except.toOption]
  have hb : lc.ctx.f.block? 1 = some blk1 := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk1, hb]
  have hval : ∀ n, (lc.ctx.f.value? n).isSome = true → lc.ctx.f.value? n = some (val n) := by
    intro n h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    simp [val, hv]
  have hE := g2Env hc
  have hpre : ∀ v : Value, v.op ≠ .ARM64CMP → v.op ≠ .ARM64CMPconst → v.op ≠ .ARM64MOVDload →
      ∀ s, G1Pre lc s v := fun v h1 h2 h3 s =>
    ⟨fun h => by rcases h with h | h <;> contradiction, fun h => absurd h h3⟩
  obtain ⟨s1, hs1, hrun⟩ := GenG1.okThen_spec hrun
  obtain ⟨s2, hs2, hrun⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨hm2, hrun⟩ := hrun
  obtain ⟨s3, hs3, hrun⟩ := GenG1.okThen_spec hrun
  obtain ⟨s4, hs4, -⟩ := GenG1.okThen_spec hrun
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, hinv1⟩ := g2_value (H := H0) hc hE hmem hb hi1 (hval 2 hv2s)
    (by rw [hop2]; rfl) (locMatch0 7) (g2Inv0 7 hcls)
    (hpre _ (by rw [hop2]; decide) (by rw [hop2]; decide) (by rw [hop2]; decide) _)
    (callOK_ne (by rw [hop2]; decide)) hs1
  have hidx : ((tab.lookup 1).getD []).getD 3 0 = ((tab.lookup 1).getD []).getD 2 0 := by decide
  have hm1' : LocMatch E1 s1 1 3 m1 := by
    refine locMatch_pc hm1 ?_
    rw [hm1.pc, hx1.1]
    show pcOfTab text ps.toList tab 1 3 = pcOfTab text ps.toList tab 1 (1 + 1)
    unfold pcOfTab
    rw [hidx]
  have hA1 := hE1.addr
  obtain ⟨E2, m2, hx2, hE2, hp2, hm2', hinv2⟩ := g2_value (H := H0) hc hE1 hmem hb hi3
    (hval 6 hv6s) (by rw [hop6]; rfl) hm1' hinv1
    (hpre _ (by rw [hop6]; decide) (by rw [hop6]; decide) (by rw [hop6]; decide) _)
    (callOK0 hA1 (hx1.2 _ _ rfl) hm2 hno) hs2
  obtain ⟨E3, m3, hx3, hE3, hp3, hm3, hinv3⟩ := g2_value (H := H0) hc hE2 hmem hb hi4
    (hval 7 hv7s) (by rw [hop7]; rfl) hm2' hinv2
    (hpre _ (by rw [hop7]; decide) (by rw [hop7]; decide) (by rw [hop7]; decide) _)
    (callOK_ne (by rw [hop7]; decide)) hs3
  obtain ⟨E4, m4, hx4, hE4, hp4, hm4, -⟩ := g2_value (H := H0) hc hE3 hmem hb hi5
    (hval 3 hv3s) (by rw [hop3]; rfl) hm3 hinv3
    (hpre _ (by rw [hop3]; decide) (by rw [hop3]; decide) (by rw [hop3]; decide) _)
    (callOK_ne (by rw [hop3]; decide)) hs4
  exact ⟨s1, s2, s3, s4, E4, m4, hs1, hs2, hs3, hs4,
    MatchEnv.Extends.trans (MatchEnv.Extends.trans (MatchEnv.Extends.trans hx1 hx2) hx3) hx4,
    hE4, ((hp1.trans hp2).trans hp3).trans hp4, hm4⟩

end GoFV.Proof.Witness.GenG2
