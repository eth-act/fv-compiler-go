import GoFV.Proof.Gen.G1
import GoFV.Gen.Genssa
import GoFV.Asm.Parse
import GoFV.SSA.Parse

/-!
# Non-vacuity witness: slice G1 of the genssa validator on `clamp`

`test/copy/main/clamp,1.ssa` and `test/copy/main/clamp,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v9/plain`, embedded verbatim (`clampSsa`, `clampProg`):

```go
func clamp(x int) int {
	if x > 40 {
		return 40
	}
	return x
}
```

`load` parses both files, runs `Env.load` and `genssa` on the exported frame (as `gen-check`), and
gives `runLoc`'s context of the function after `trim`, genssa's P0 Progs and block starts. By
compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`, as
`verifiedPipeline_witness`; `clampFacts`), `checkG1` accepts them with the PC table `tab`, and
from the state after the entry values with `x = 50` (and `x = 30`) in `R0`, `stepLoc` runs the
compare `v7` (`CMPconst [40]`) and `stepTermLoc` the `GT` block `b1` to `b3` (`return 40`; for
`x = 30`, `b2`, `return x`). On an activation with `G1Env` (frameless, `ι` only the nil block,
the Progs at `0x10000 + 4·ID`, `ret = 0`), `g1_value` and then `g1_term` give machine runs of the
Progs (`CMP $40, R0`; `BLE` taken to `b2` or falling through to `b3`) to a state related by
`LocMatch` before the successor's first value (`genG1_witness_50`, `genG1_witness_30`).
-/

namespace GoFV.Proof.Witness.GenG1

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/copy/main/clamp,1.ssa` (quick-v9). -/
def clampSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "clamp" 1 0 0
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
type t2 INT 8 8 0 comparable,named "int" "int"
type t1 FUNC 8 8 8 hasptr,direct "func(int) int" "func(int) int" 0 1 1
field 0 "n" t2 ? 0
field 1 "" t2 ? 0
aux a2 sym "main.clamp" "main.clamp" 1 - 0 - - - - 0
posbase p2 "./copy.go" 1 1 -1
aux a3 name "n" "n" PPARAM t2 0 1 used p2:89:12:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t2 0 1 - p2:89:19:0:0
aux a1 call "AuxCall{main.clamp}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t4 INT8 1 1 0 comparable,named "int8" "int8"
type t5 INT16 2 2 0 comparable,named "int16" "int16"
type t6 INT32 4 4 0 comparable,named "int32" "int32"
type t7 INT64 8 8 0 comparable,named "int64" "int64"
type t8 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t9 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t10 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t11 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t12 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t13 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t2
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
type t33 RESULTS ? ? ? - "int,mem" "" 2 t2,t28
slot s1 a3 t2 0 - 0
f b1 t1 a1 14 3
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t2,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t20 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:0:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v12 Copy t2 0 - p2:93:2:2:0 1 v6
v v13 Copy t28 0 - p2:93:2:2:0 1 v1
v v14 MakeResult t33 0 - p2:93:2:0:0 1 v12,v13
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v10 Copy t28 0 - p2:91:3:2:0 1 v1
v v11 MakeResult t33 0 - p2:91:3:0:0 1 v8,v10
names s1
named s1 v6,v12
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,40=v8
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t20 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v12 Copy t2 0 - p2:93:2:2:0 1 v6
v v13 Copy t28 0 - p2:93:2:2:0 1 v1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v12,v13
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v10 Copy t28 0 - p2:91:3:2:0 1 v1
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v10
names s1
named s1 v6,v12
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,40=v8
freev -
freeb -
cache postorder b3,b2,b1
cache linestarts 2:90:93
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 6 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t20 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:89:6:2:0 3 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v12 Copy t2 0 - p2:93:2:2:0 0 v6
v v13 Copy t28 0 - p2:93:2:2:0 0 v1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v10 Copy t28 0 - p2:91:3:2:0 0 v1
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6,v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,40=v8
freev -
freeb -
cache postorder b3,b2,b1
cache linestarts 2:90:93
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 2:90:93
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 2:90:93
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 2:90:93
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 2:90:93
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 2:90:93
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 2:90:93
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 2:90:93
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:89:6:2:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v10,v13,v12,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "n+0" a3 0
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v13 SP t15 0 - p0:0:0:0:0 3 -
v v12 OffPtr t20 0 - p0:0:0:0:0 0 v13
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
v v7 LocalAddr t20 0 a4 p2:93:2:1:0 0 v13,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
v v5 LocalAddr t20 0 a4 p2:91:3:1:0 0 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v12,40=v8
freev v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v13 SP t15 0 - p0:0:0:0:0 3 -
v v12 OffPtr t20 0 - p0:0:0:0:0 0 v13
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
v v7 LocalAddr t20 0 a4 p2:93:2:1:0 0 v13,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
v v5 LocalAddr t20 0 a4 p2:91:3:1:0 0 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v12,40=v8
freev v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v13 SP t15 0 - p0:0:0:0:0 3 -
v v12 OffPtr t20 0 - p0:0:0:0:0 0 v13
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
v v7 LocalAddr t20 0 a4 p2:93:2:1:0 0 v13,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
v v5 LocalAddr t20 0 a4 p2:91:3:1:0 0 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v12,40=v8
freev v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v13 SP t15 0 - p0:0:0:0:0 3 -
v v12 OffPtr t20 0 - p0:0:0:0:0 0 v13
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
v v7 LocalAddr t20 0 a4 p2:93:2:1:0 0 v13,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
v v5 LocalAddr t20 0 a4 p2:91:3:1:0 0 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v12,40=v8
freev v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v5,v7,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v5,v7,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v5,v7,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v5,v7,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v5,v7,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v5,v7,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v5,v7,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v5,v7,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 14 3
b b1 If p2:90:9:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 Const64 t2 40 - p0:0:0:0:0 2 -
v v9 Less64 t3 0 - p2:90:7:1:0 1 v8,v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 40=v8
freev v5,v7,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 2:90:93
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v8 ARM64MOVDconst t2 40 - p0:0:0:0:0 1 -
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v8,v1
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v9,v12,v13,v10,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{main.clamp}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v5 ARM64MOVDconst t2 40 - p2:91:3:2:0 1 -
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v5,v1
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v9,v10,v12,v13
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
fstate scheduled,laidout
regalloc 15 v5:R0,v6:R0,v11:[],v14:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v5 ARM64MOVDconst t2 40 - p2:91:3:2:0 1 -
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v5,v1
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v9,v10,v12,v13
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
fstate scheduled,laidout
regalloc 15 v5:R0,v6:R0,v11:[],v14:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 14 3
b b1 ARM64GT p2:90:9:0:0 0 0 - v7 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p2:90:9:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 ARM64CMPconst t29 40 - p2:90:7:1:0 1 v6
b b3 Ret p2:91:10:1:0 0 0 - v11 - b1:0
v v5 ARM64MOVDconst t2 40 - p2:91:3:2:0 1 -
v v11 MakeResult t33 0 - p2:91:3:1:0 1 v5,v1
b b2 Ret p2:93:2:1:0 0 0 - v14 - b1:1
v v14 MakeResult t33 0 - p2:93:2:1:0 1 v6,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v9,v10,v12,v13
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:90:93
fstate scheduled,laidout
regalloc 15 v5:R0,v6:R0,v11:[],v14:[]
dcllen 2
end
frontend
end
ptrcache t2,t5,t6,t7,t8,t10,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t2,t14,t15,t25,t26,t12,t13,t3,t17,t18,t19,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t33
eof
"#

/-- `test/copy/main/clamp,1.prog` (quick-v9). -/
def clampProg : String := r#"gofv-prog 2
pkg "main"
func "clamp" 1
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
type t1 8 8 0 0 - "int"
name n1 "n" PPARAM t1 1 "main.n" 0 a3
name n2 "~r0" PPARAMOUT t1 1 "main.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p2 "./copy.go" 1 1 -1 1
sym y1 "main.clamp" 1
curfn p2:89:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 89 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "main.clamp.arginfo1" 0
sym y4 "main.clamp.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:89:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:89:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:89:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:89:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:89:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:89:6:2:0
p 6 6 0 0 0 - CMP 0 CONST/0/0/0/NONE/0/40/-/- 8192 - _ 0 0 p2:90:7:1:0
p 7 7 0 0 0 - BLE 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@10 0 0 p2:90:9:2:0
p 8 8 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/40/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:91:3:1:0
p 9 9 0 0 0 - RET 0 _ 0 - _ 0 0 p2:91:10:2:0
p 10 10 0 0 0 - RET 0 _ 0 - _ 0 0 p2:93:2:1:0
p 11 11 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 89 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p2:89:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:89:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:89:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:89:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:89:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:89:6:2:0
p 6 0 0 0 96 - CMP 0 CONST/0/0/0/NONE/18/40/-/- 8192 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:90:7:1:0
p 7 4 0 0 80 - BLE 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/10/-/@10 0 0 p2:90:9:2:0
p 8 8 0 0 318 - MOVD 0 CONST/0/0/0/NONE/18/40/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:91:3:1:0
p 9 12 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:91:10:2:0
p 10 16 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:93:2:1:0
fn y1 8 0 0 0 89 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 32 0 1fa000f16d000054000580d2c0035fd6c0035fd6000000000000000000000000 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 0 1 28000 - 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040800 0
data y9 SRODATA 3 1 28000 020800 0
data y10 SRODATA 3 1 28000 040800 0
data y11 SRODATA 8 1 28000 b601020202040400 0
data y12 SRODATA 3 1 28000 000800 0
end
eof
"#

/-- `runLoc`'s context of the function after `trim`, genssa's P0 Progs in list order and the
Prog ID of each block's start (as `gen-check`). -/
def load (ssa prog : String) :
    Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat)) := do
  let (e, _) ← GoFV.SSA.parseExportExt ssa.toUTF8
  let pf ← GoFV.Asm.parseProgFile prog.toUTF8
  let env ← GoFV.Gen.Env.load e pf
  let fr : GoFV.Gen.FrameOut :=
    { dcl := pf.frame.dclOut, optDcl := pf.frame.optDcl, merges := pf.frame.merges,
      stksize := pf.frame.stksize, stkptrsize := pf.frame.stkptrsize,
      stkalign := pf.frame.stkalign }
  let out ← GoFV.Gen.genssa env fr
  return (LocCtx.make env.tabs env.f, out.order.filterMap (out.st.progs[·]?),
    fun b => (out.st.bstart[b]?).join)

/-- The loaded `clamp`. -/
def clampIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat)) :=
  load clampSsa clampProg

def lc : LocCtx :=
  match clampIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

def ps : Array GoFV.Asm.Prog :=
  match clampIn with
  | .ok x => x.2.1
  | .error _ => #[]

def bs : ID → Option Nat :=
  match clampIn with
  | .ok x => x.2.2
  | .error _ => fun _ => none

/-- The PC table `checkG1` gives: per block, the index of each value's first Prog and of the
terminator's. -/
def tab : PcTab := [(1, [5, 5, 5, 7]), (3, [8, 9, 9]), (2, [10, 10])]

/-- Block `b1` (`v6 = ArgIntReg`, `v1 = InitMem`, `v7 = CMPconst [40] v6`; `GT` to `b3`, `b2`). -/
def blk1 : Block := (lc.ctx.f.block? 1).getD default

def v7 : Value := (lc.ctx.f.value? 7).getD default

/-- The empty memory. -/
def mem0 : Mem := {}

/-- The `runLoc` state after the entry values: `x` in `R0`, every other register `poison`. -/
def s0 (x : BitVec 64) : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .i64 x else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- `f` of the result of a successful step, else `false`. -/
def okThen {α : Type} (r : Res α) (f : α → Bool) : Bool :=
  match r with
  | .ok a => f a
  | _ => false

theorem okThen_spec {α : Type} {r : Res α} {f : α → Bool} (h : okThen r f = true) :
    ∃ a, r = .ok a ∧ f a = true := by
  unfold okThen at h
  split at h
  · exact ⟨_, rfl, h⟩
  · cases h

/-- The terminator goes to block `t`. -/
def gotoIs (n : Next) (t : ID) : Bool :=
  match n with
  | .goto e => e.b == t
  | _ => false

theorem gotoIs_spec {n : Next} {t : ID} (h : gotoIs n t = true) : ∃ e, n = .goto e ∧ e.b = t := by
  unfold gotoIs at h
  split at h
  · exact ⟨_, rfl, beq_iff_eq.1 h⟩
  · cases h

/-- What compiled evaluation checks: `checkG1` accepts `clamp` with `tab`; `b1` is laid out and
holds `v7` at index 2; `R0` holds 64-bit values; the compare reads an integer; and `stepLoc` of
`v7` then `stepTermLoc` of `b1` go to block `t`. -/
def clampFacts (x : BitVec 64) (t : ID) : Bool :=
  (checkG1 lc ps bs).toOption == some tab && lc.ctx.f.blocks.toList.contains 1 &&
    (lc.ctx.f.block? 1).isSome && (lc.ctx.f.value? 7).isSome && blk1.values[2]? == some 7 &&
    blk1.values.size == 3 && blk1.kind == .ARM64GT && v7.op == .ARM64CMPconst &&
    regCls lc 0 == some 64 &&
    v7.args.toList.all (fun a => match (s0 x).read lc a with
      | .ok (.ptr _) => false
      | _ => true) &&
    okThen (stepLoc default lc (s0 x) v7) fun s1 =>
      okThen (stepTermLoc lc s1 blk1) fun r => gotoIs r.1 t

/-- `clamp` from the state after its entry values: to `b3` for `x = 50`, to `b2` for `x = 30`. -/
theorem clamp_facts : (clampFacts 50 3 && clampFacts 30 2) = true := by
  native_decide

/-- The text base of the layout. -/
def text : BitVec 64 := 0x10000

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`. -/
def L : Link := Link.byId (fun _ => 0) text 0 0 ps.toList

/-- `ι`: only the nil block (no live block). -/
def ι : Blk → Option (BitVec 64)
  | .nil => some 0
  | _ => none

/-- A frameless activation (`SP = 0x7fff0000`, `g = 0x9000`, `LR = 0x40`, `FP = 0`) with the PC
table of `checkG1`. -/
def E : MatchEnv :=
  { lc, ι, sp := 0x7fff0000, slot := fun _ => none, g := 0x9000, lr := 0x40, fp := 0,
    framed := false, pcOf := pcOfTab text ps.toList tab }

/-- The machine before `v7`: `X0 = x`, the activation's `g`, `FP`, `LR`, the PC of `v7`. -/
def m0 (x : BitVec 64) : MState :=
  { x := fun k => if k = 0 then x else if k = 28 then 0x9000 else if k = 29 then 0 else
      if k = 30 then 0x40 else 0,
    sp := 0x7fff0000, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := fun _ => 0 }

theorem addrAgree : AddrAgree ι := by
  intro b n a hb ha
  cases b <;> simp [ι] at ha
  simp [Blk.base?] at hb
  subst hb; subst ha; rfl

theorem memInj0 (mm : Memory) : MemInj ι mem0 mm where
  nil := rfl
  mapped := by intro b al h; simp [mem0] at h
  inj := by intro b al b' al' a a' h; simp [mem0] at h
  bytes := ⟨fun _ _ => False, by intro b al a h; simp [mem0] at h⟩

theorem g1Env (hc : checkG1 lc ps bs = .ok tab) : G1Env lc L ps 0 tab E where
  lc := rfl
  link := rfl
  pcOf := rfl
  ret := by
    obtain ⟨-, -, -, -, -, -, hlt, -, -⟩ := checkG1_spec hc
    intro p hp h
    rw [L, addr_byId hp] at h
    have hid := hlt p hp
    have := congrArg BitVec.toNat (Option.some.inj h)
    simp [text, BitVec.toNat_add] at this
    omega
  addr := addrAgree
  leaf := rfl

theorem locMatch0 (x : BitVec 64) : LocMatch E (s0 x) 1 2 (m0 x) where
  regs := by
    intro r v hv
    simp only [s0, Array.getElem?_ofFn] at hv
    split at hv
    · rename_i hr
      simp only [Option.some.injEq] at hv
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
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, (fun h => by cases h), fun _ => ⟨rfl, rfl⟩⟩
  pc := rfl

theorem g1Inv0 (x : BitVec 64) (h0 : regCls lc 0 = some 64) : G1Inv lc (s0 x) where
  slots := rfl
  regs := by
    intro r v c hr hv hc
    simp only [s0, Array.getElem?_ofFn] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      split at hv
      · rename_i h0'
        subst hv; subst h0'
        rw [h0] at hc; cases hc; rfl
      · subst hv; trivial
    · cases hv
  mem := ⟨mem0, rfl, by simp [KeysNodup, mem0]⟩

/-- Both theorems on `clamp`: from the state after the entry values, the compare `v7` and the
terminator of `b1` are matched by runs of genssa's P0 Progs to a state related before the first
value of the block `runLoc` goes to. -/
theorem genG1_witness (H : Hooks) (x : BitVec 64) (t : ID) (hf : clampFacts x t = true) :
    ∃ s1 s2 e m2, stepLoc default lc (s0 x) v7 = .ok s1 ∧
      stepTermLoc lc s1 blk1 = .ok (.goto e, s2) ∧ e.b = t ∧
      PStar H L ps.toList 0 (m0 x) m2 ∧ LocMatch E s2 t 0 m2 := by
  simp only [clampFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.all_eq_true]
    at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, hmem⟩, hbs⟩, hvs⟩, hv2⟩, hsz⟩, hkind⟩, hop⟩, hcls⟩, hargs⟩, hrun⟩ := hf
  have hc : checkG1 lc ps bs = .ok tab := by
    revert hck; cases checkG1 lc ps bs <;> simp [Except.toOption]
  have hb : lc.ctx.f.block? 1 = some blk1 := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk1, hb]
  have hv : lc.ctx.f.value? 7 = some v7 := by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [v7, hv]
  have hE := g1Env hc
  have hen : entryOp v7.op = false := by rw [hop]; rfl
  have hpre : G1Pre lc (s0 x) v7 := by
    refine ⟨fun _ a ha y hy p hp => ?_, fun h => by rw [hop] at h; cases h⟩
    have := hargs a ha
    rw [hy, hp] at this
    cases this
  obtain ⟨s1, hs1, hrun⟩ := okThen_spec hrun
  obtain ⟨⟨n, s2⟩, hs2, hrun⟩ := okThen_spec hrun
  obtain ⟨e, rfl, het⟩ := gotoIs_spec hrun
  obtain ⟨m1, hp1, hm1, hinv1⟩ := g1_value (H := H) hc hE hmem hb hv2 hv hen (locMatch0 x)
    (g1Inv0 x hcls) hpre hs1
  have hm1' : LocMatch E s1 1 blk1.values.size m1 := by rw [hsz]; exact hm1
  obtain ⟨m2, hp2, hm2, -, -⟩ := g1_term (H := H) hc hE hmem hb hm1' hinv1
    (fun hz => by rw [hkind] at hz; rcases hz with h | h <;> cases h) hs2
  exact ⟨s1, s2, e, m2, hs1, hs2, het, hp1.trans hp2, het ▸ hm2⟩

theorem genG1_witness_50 (H : Hooks) :
    ∃ s1 s2 e m2, stepLoc default lc (s0 50) v7 = .ok s1 ∧
      stepTermLoc lc s1 blk1 = .ok (.goto e, s2) ∧ e.b = 3 ∧
      PStar H L ps.toList 0 (m0 50) m2 ∧ LocMatch E s2 3 0 m2 := by
  have h := clamp_facts
  simp only [Bool.and_eq_true] at h
  exact genG1_witness H 50 3 h.1

theorem genG1_witness_30 (H : Hooks) :
    ∃ s1 s2 e m2, stepLoc default lc (s0 30) v7 = .ok s1 ∧
      stepTermLoc lc s1 blk1 = .ok (.goto e, s2) ∧ e.b = 2 ∧
      PStar H L ps.toList 0 (m0 30) m2 ∧ LocMatch E s2 2 0 m2 := by
  have h := clamp_facts
  simp only [Bool.and_eq_true] at h
  exact genG1_witness H 30 2 h.2

end GoFV.Proof.Witness.GenG1
