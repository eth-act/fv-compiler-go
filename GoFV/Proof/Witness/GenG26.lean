import GoFV.Proof.Gen.G26
import GoFV.Proof.Witness.GenG25

/-!
# Non-vacuity witness: slice G26 of the genssa validator on `main.func1` of examples/generics

`examples/generics/main/main.func1,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`): the closure
`func(x int) int { return x }` of `examples/generics` (line 37). Its trimmed body holds no arm64
op: `v11 = ArgIntReg` (in `R2`), `InitMem`, `v12 = Copy v11` (in `R0`), `MakeResult`, a `Ret`
block. So `runLoc` runs it in Phase 1's mode, and `checkG25` rejects it (`not lowered`).
`checkG26` accepts it with the PC table `tab` and the class table `kt`. genssa emits the `Copy`
as `MOVD R2, R0`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g26_facts`),
`stepLoc` runs `v12` from a state with `x = 7` in `R2`, and `R0` then holds 7. On a framed
activation with `G10Env` (as `GenG25`'s) with `X2 = 7`, `g26_value` runs the `MOVD`: the machine's
`X0` is 7 (`genG26_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG26

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `examples/generics/main/main.func1,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "main.func1" 1 0 0
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
type t3 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t4 INT 8 8 0 comparable,named "int" "int"
type t2 STRUCT 24 8 8 hasptr,comparable,named "pair[string,int]" "main.pair[string,int]" 2
field 0 "k" t3 0 0
field 1 "v" t4 16 0
type t1 FUNC 8 8 8 hasptr,direct "func(pair[string,int]) int" "func(main.pair[string,int]) int" 0 1 1
field 0 "p" t2 ? 0
field 1 "" t4 ? 0
aux a2 sym "main.main.func1" "main.main.func1" 1 - 0 - - - - 0
posbase p2 "./main.go" 1 1 -1
aux a3 name "p" "p" PPARAM t2 0 1 used p2:37:22:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t4 0 1 - p2:37:43:0:0
aux a1 call "AuxCall{main.main.func1}" a2 1 1 1 8 24 3 1
abiparam in 0 t2 a3 0,1,2 0
abiparam out 0 t4 a4 0 -1
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
type t18 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t10
type t19 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t8
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t12
type t21 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t4
type t22 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t17
type t23 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t14
type t24 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t15
type t25 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t18
type t26 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t27 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t28 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t29 SSA ? ? ? - "mem" ""
type t30 SSA ? ? ? - "flags" ""
type t31 SSA ? ? ? - "void" ""
type t32 SSA 16 8 ? - "int128" ""
type t33 RESULTS ? ? ? - "mem" "" 1 t29
type t34 PTR 8 8 8 hasptr,direct,comparable "*pair[string,int]" "*main.pair[string,int]" t2
type t35 RESULTS ? ? ? - "int,mem" "" 2 t4,t29
slot s1 a3 t2 0 - 0
f b1 t1 a1 9 1
typs Bool=t5,Int8=t6,Int16=t7,Int32=t8,Int64=t9,UInt8=t10,UInt16=t11,UInt32=t12,UInt64=t13,Int=t4,Float32=t14,Float64=t15,UInt=t16,Uintptr=t17,String=t3,BytePtr=t18,Int32Ptr=t19,UInt32Ptr=t20,IntPtr=t21,UintptrPtr=t22,Float32Ptr=t23,Float64Ptr=t24,BytePtrPtr=t25,Complex64=t26,Complex128=t27,UnsafePtr=t28,Mem=t29,Flags=t30,Void=t31,Int128=t32,ResultMem=t33
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v7 Const64 t4 0 - p0:0:0:0:0 0 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v7 Const64 t4 0 - p0:0:0:0:0 0 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:37:37
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v7 Const64 t4 0 - p0:0:0:0:0 0 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:37:37
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:37:37
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:37:37
dcllen 2
end
pass 5 "decompose user"
slot s2 a3 t3 0 - 0
slot s3 a3 t4 16 - 0
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names s2,s3
named s2 -
named s3 -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:37:37
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:37:37
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:37:37
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:37:37
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:37:37
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 9 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:37:17:2:0 1 -
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "p+0" a3 0
aux a6 nameoff "p+8" a3 8
aux a7 nameoff "p+16" a3 16
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 StructMake t2 0 - p2:37:57:2:0 1 v10,v11
v v8 StructSelect t4 1 - p2:37:57:0:0 1 v6
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v8,v1
v v7 SB t17 0 - p0:0:0:0:0 0 -
v v5 SP t17 0 - p0:0:0:0:0 2 -
v v4 OffPtr t34 0 - p0:0:0:0:0 0 v5
v v3 ArgIntReg t18 0 a5 p2:37:57:2:0 1 -
v v2 ArgIntReg t4 1 a6 p2:37:57:2:0 1 -
v v10 StringMake t3 0 - p2:37:57:2:0 1 v3,v2
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
v v12 LocalAddr t21 0 a4 p2:37:49:1:0 0 v5,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts 0=v4
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 StructMake t2 0 - p2:37:57:2:0 0 v10,v11
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v7 SB t17 0 - p0:0:0:0:0 0 -
v v5 SP t17 0 - p0:0:0:0:0 2 -
v v4 OffPtr t34 0 - p0:0:0:0:0 0 v5
v v3 ArgIntReg t18 0 a5 p2:37:57:2:0 1 -
v v2 ArgIntReg t4 1 a6 p2:37:57:2:0 1 -
v v10 StringMake t3 0 - p2:37:57:2:0 1 v3,v2
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 2 -
v v12 LocalAddr t21 0 a4 p2:37:49:1:0 0 v5,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts 0=v4
freev v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 StructMake t2 0 - p2:37:57:2:0 0 v10,v11
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v7 SB t17 0 - p0:0:0:0:0 0 -
v v5 SP t17 0 - p0:0:0:0:0 2 -
v v4 OffPtr t34 0 - p0:0:0:0:0 0 v5
v v3 ArgIntReg t18 0 a5 p2:37:57:2:0 1 -
v v2 ArgIntReg t4 1 a6 p2:37:57:2:0 1 -
v v10 StringMake t3 0 - p2:37:57:2:0 1 v3,v2
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 2 -
v v12 LocalAddr t21 0 a4 p2:37:49:1:0 0 v5,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts 0=v4
freev v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 StructMake t2 0 - p2:37:57:2:0 0 v10,v11
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v7 SB t17 0 - p0:0:0:0:0 0 -
v v5 SP t17 0 - p0:0:0:0:0 2 -
v v4 OffPtr t34 0 - p0:0:0:0:0 0 v5
v v3 ArgIntReg t18 0 a5 p2:37:57:2:0 1 -
v v2 ArgIntReg t4 1 a6 p2:37:57:2:0 1 -
v v10 StringMake t3 0 - p2:37:57:2:0 1 v3,v2
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 2 -
v v12 LocalAddr t21 0 a4 p2:37:49:1:0 0 v5,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts 0=v4
freev v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:37:37
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v11,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v12,v10,v2,v3,v4,v5,v7,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{main.main.func1}" a2 1 1 1 8 24 3 1
abiparam in 0 t2 a3 0,1,2 0
abiparam out 0 t4 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v12 Copy t4 0 - p2:37:49:2:0 1 v11
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v12,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v6,v7,v8,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
fstate scheduled,laidout
regalloc 13 v9:[],v11:R2,v12:R0
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v12 Copy t4 0 - p2:37:49:2:0 1 v11
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v12,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v6,v7,v8,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
fstate scheduled,laidout
regalloc 13 v9:[],v11:R2,v12:R0
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 12 1
b b1 Ret p2:37:57:1:0 0 0 - v9 - -
v v11 ArgIntReg t4 2 a7 p2:37:57:2:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v12 Copy t4 0 - p2:37:49:2:0 1 v11
v v9 MakeResult t35 0 - p2:37:49:1:0 1 v12,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2,s1/16/t4=s3
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v6,v7,v8,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 2:37:37
fstate scheduled,laidout
regalloc 13 v9:[],v11:R2,v12:R0
dcllen 2
end
frontend
end
ptrcache t3,t4,t7,t8,t9,t10,t12,t14,t15,t17,t18,t25
typelink t29=t33
typeorder t6,t10,t7,t11,t8,t12,t9,t13,t4,t16,t17,t26,t27,t14,t15,t5,t18,t19,t20,t21,t22,t23,t24,t25,t34,t1,t2,t3,t28,t29,t31,t30,t32,t33,t35
eof
"#

/-- `examples/generics/main/main.func1,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "main.func1" 1
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
type t1 24 8 8 1 01 "pair[string,int]"
name n1 "p" PPARAM t1 1 "main.p" 0 a3
type t2 8 8 0 0 - "int"
name n2 "~r0" PPARAMOUT t2 1 "main.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p2 "./main.go" 1 1 -1 1 "./main.go" "./main.go" 1 1
type t3 8 8 8 1 01 "*uint8"
sym y1 "main.main.func1" 1
curfn p2:37:17:0:0 0 0
regargs 8192:0:t3,8193:8:t2,8194:16:t2
text y1 0 0 0 0 37 208080
end
prog0
sym y2 "main.p" 0
sym y3 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y4 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y5 "main.main.func1.arginfo1" 0
sym y6 "main.main.func1.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i24 0 0 p2:37:17:0:0
p 9 9 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/PARAM/0/0/y2/- 0 0 p2:37:17:2:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:37:17:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:37:17:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:37:17:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p2:37:17:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:37:17:2:0
p 6 6 0 0 0 - MOVD 0 REG/8194/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:37:49:1:0
p 7 7 0 0 0 - RET 0 _ 0 - _ 0 0 p2:37:57:2:0
p 8 8 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 37 208080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 0 MOVD MOVD
funcaux y3 y4 - - y5 y6 -
needzero -
regargs -
text 0 0 - 0
symalign y3:4,y4:4,y5:1,y6:1
autot -
dbgentry 1
dbgslot 0 n1 t2 16
dbgslot 1 n1 t3 0
dbgslot 2 n1 t2 8
dbgvar 0 n1 1,2,0
dbgloc 0 1:-10000:1:12:509308519308529308,1:12:-1:-30000:9308519308529308
dbgregout n2
dbgpc 1:12:7
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i24 0 2 p2:37:17:0:0
p 9 0 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/0/y2/- 0 0 p2:37:17:2:0
p 1 4 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:37:17:0:0
p 2 4 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:37:17:0:0
p 3 4 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p2:37:17:0:0
p 4 4 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y6/- 0 0 p2:37:17:0:0
p 5 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:37:17:2:0
p 6 4 0 0 301 - MOVD 0 REG/8194/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:37:49:1:0
p 7 8 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:37:57:2:0
fn y1 24 0 0 0 37 2080c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 0 MOVD MOVD
funcaux y3 y4 - - y5 y6 -
text 16 0 e00700f9e00302aac0035fd600000000 0
pcln y11 y12 y13 y14 y7,y8,y9,y10 y3,y4,_,_,_,y5,y6
usedfiles 1
data y3 Sxxx 0 4 8000 02000000010000000100 0
data y4 Sxxx 0 4 8000 0200000000000000 0
data y5 SDATA 11 1 8000 fefe00080808fd1008fdff 0
data y6 SDATA 2 1 8000 0000 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 0 1 28000 - 0
data y10 SRODATA 5 1 28000 0001040300 0
data y11 SRODATA 3 1 28000 020400 0
data y12 SRODATA 3 1 28000 040400 0
data y13 SRODATA 3 1 28000 4c0400 0
data y14 SRODATA 3 1 28000 000400 0
end
dwarf
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "go:info.main.pair[string,int]" 0
sym y20 "go:info.int" 0
sym y21 "type:int" 0
dwfn y15 y16 y17 - y18 "main.main.func1" 1:37 1 0 1 9
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "main.pair[string,int]" 0 0 1 p2:37:22:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "int" 0 0 1 p2:37:43:0:0
var 0 0 "p" 5 1 0 0 0 8 y19 "./main.go" 37 22 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y20 "./main.go" 37 43 0 1 0 0 -
scope 0 0 - 0,1
data y15 SDWARFFCN 53 0 0 036d61696e2e6d61696e2e66756e6331000010019c0200000025012d7000002500000000000000002e7e7230000125000000000000 5
reloc 0 0 R_USETYPE 0 y21
reloc 17 1 R_DWTXTADDR_U1 0 y1
reloc 32 4 R_DWARFSECREF 0 y19
reloc 36 4 R_DWARFSECREF 0 y16
reloc 47 4 R_DWARFSECREF 0 y20
data y16 SDWARFLOC 28 0 0 01000400080950930851930852930804081008930851930852930800 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y17 SDWARFRANGE 0 0 0 - 0
data y18 SDWARFLINES 26 0 0 0009020000000000000000040206031f14063706370208000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded closure (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG26` gives (`b1`: one entry per value `v11`, `v1`, `v12`, `v9`, then the
`RET`). -/
def tab : PcTab := [(1, [6, 6, 6, 8, 8])]

/-- The class table `checkG26` gives (nothing known at the entry). -/
def kt : KTab := (match checkG26 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG26`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The empty memory. -/
def mem0 : Mem := {}

/-- The `runLoc` state before `v12`: the argument `x = 7` in `R2`, every other register `poison`.
-/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 2 then .int .w64 7 else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v12`: `X2 = 7`, the activation's `g` and `FP`, the PC of `v12`, a zero
memory. -/
def m0 : MState :=
  { x := fun k => if k = 2 then 7 else if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8
      else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := fun _ => 0 }

/-- The register holds the 64-bit integer 7. -/
def is7 : Option Val → Bool
  | some (.int .w64 x) => x == 7
  | _ => false

theorem is7_spec {o : Option Val} (h : is7 o = true) : o = some (.int .w64 7) := by
  unfold is7 at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on the closure: it holds no arm64 op, `checkG26` accepts it
with `tab` and `kt` and `checkG25` does not; it accesses no frame variable and has no home slot;
`b1` holds `v12` (`Copy`) at index 2, `R2` has class 64 before `v12` and nothing is in the
upper-bit table there; `stepLoc` runs `v12` from `s0` to `R0 = 7`. -/
def gFacts : Bool :=
  !lc.ctx.f.lowered &&
    (checkG26 lc ps bs g).toOption == some (tab, kt) && (checkG25 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 12).isSome && blk1.values[2]? == some 12 && (val 12).op == .Copy &&
    (kAt lc kt 1 blk1 2).get 2 == some 64 && uAt lc blk1 2 == none &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 12)) fun s1 => is7 s1.regs[0]?

theorem g26_facts : gFacts = true := by
  native_decide

/-- The facts of `g26_facts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = false ∧ checkG26 lc ps bs g = .ok (tab, kt) ∧
      (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 1 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 1 = some blk1 ∧ lc.ctx.f.value? 12 = some (val 12) ∧
      blk1.values[2]? = some 12 ∧ (val 12).op = .Copy ∧
      (kAt lc kt 1 blk1 2).get 2 = some 64 ∧ uAt lc blk1 2 = none ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 12)) (fun s1 => is7 s1.regs[0]?) = true := by
  have hf := g26_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, Bool.not_eq_true'] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hres⟩, -⟩, hav⟩, hsl⟩, hm1⟩, hb1s⟩, hv12s⟩, hi2⟩, hop⟩, hk2⟩, hu⟩,
    hrun⟩ := hf
  refine ⟨hl, ?_, hav, hsl, hm1, ?_, ?_, hi2, hop, hk2, hu, hrun⟩
  · revert hres; cases checkG26 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [blk1, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv12s
    simp [val, hv]

theorem g26Env (hc : checkG26 lc ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = false)
    (hav : (accessedVars lc).isEmpty = true) (hsl : (homeSlots lc).isEmpty = true) :
    G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkNL_spec (checkG26_nl hl hc)
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := GenG12.addrAgree
        glob := fun _ _ _ _ => rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkNL_spec (checkG26_nl hl hc)
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
    (r = 2 ∧ x = .int .w64 7) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h2; exact Or.inl ⟨h2, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 2 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
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

theorem g26Inv0 (h2 : (kAt lc kt 1 blk1 2).get 2 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk1 2) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h2] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v12`, the `Copy`: none apply. -/
theorem pre12 {s : LocState} (hop : (val 12).op = .Copy) : G14Pre lc s (val 12) := by
  have hne : ∀ o : Op, o ≠ .Copy → (val 12).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G26 on `main.func1` of examples/generics**: from the state before `v12` with `x = 7` in
`R2` (`X2 = 7`), `g26_value` runs the `Copy` (`v12`, `MOVD R2, R0`) in Phase 1's mode: `runLoc`'s
`R0` holds 7 and the machine state, related to it before `v9` under an activation extending `E`,
has `X0 = 7`. -/
theorem genG26_value_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 12) = .ok s1 ∧ s1.regs[0]? = some (.int .w64 7) ∧
      E.Extends E1 ∧ G10Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E1 s1 1 3 m1 ∧ m1.x 0 = 7 := by
  obtain ⟨hl, hc, hav, hsl, hm1, hb, hv12, hi2, hop, hk2, hu, hrun⟩ := facts
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hr1' := is7_spec hr1
  have hE := g26Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .Copy → (val 12).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g26_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm1 hb hi2 hv12 (by rw [hop]; rfl) locMatch0 (g26Inv0 hk2) (by rw [hu]; trivial)
    (pre12 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  exact ⟨s1, E1, m1, hs1, hr1', hx1, hE1, hp1, hm1',
    valRel_i64 hA ((hm1'.regs 0 _ hr1').1 0 rfl)⟩

end GoFV.Proof.Witness.GenG26
