import GoFV.Proof.Gen.G23
import GoFV.Proof.Witness.GenG22

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G23 of the genssa validator on `bytes.shouldUseASCIISet`

`std/std/bytes/shouldUseASCIISet,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`):
`shouldUseASCIISet` (`bytes/bytes.go`), `return len(chars) > 8`.

`checkG22` rejects it (`v9 = GreaterThan`); `checkG23` accepts it with the PC table `tab` and the
class table `kt`. Block `b1`: `v4 = CMPconst [8] v6` (`CMP $8, R0`) and `v9 = GreaterThan v4`
(`CSET GT, R0`), then the `RET`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g23_facts`),
`stepLoc` runs `v4` and `v9` from a state with `len(chars) = 10` in `R0`: `R0` then holds the
boolean `true`. On a framed activation with `G10Env` (as `GenG22`'s) and `X0 = 10`, `g23_value`
runs the compare, whose flags `LocMatch` relates to `NZCV`, and then the `CSET`: the machine's `X0`
is 1 (`genG23_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG23

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/bytes/shouldUseASCIISet,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "bytes"
func "shouldUseASCIISet" 1 0 0
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
config localpkg "bytes"
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
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t1 FUNC 8 8 8 hasptr,direct "func(int) bool" "func(int) bool" 0 1 1
field 0 "bufLen" t2 ? 0
field 1 "" t3 ? 0
aux a2 sym "bytes.shouldUseASCIISet" "bytes.shouldUseASCIISet" 1 - 0 - - - - 0
posbase p5 "bytes/bytes.go" 1 1 -1
aux a3 name "bufLen" "bufLen" PPARAM t2 0 1 used p5:969:24:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t3 0 1 - p5:969:36:0:0
aux a1 call "AuxCall{bytes.shouldUseASCIISet}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
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
type t33 PTR 8 8 8 hasptr,direct,comparable "*bool" "*bool" t3
type t34 RESULTS ? ? ? - "bool,mem" "" 2 t3,t28
slot s1 a3 t2 0 - 0
f b1 t1 a1 10 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t2,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v7 ConstBool t3 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:0:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,8=v8
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v7 ConstBool t3 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,8=v8
freev -
freeb -
cache postorder b1
cache linestarts 5:970:970
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v7 ConstBool t3 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,8=v8
freev -
freeb -
cache postorder b1
cache linestarts 5:970:970
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:970:970
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:970:970
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:970:970
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:970:970
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:970:970
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:970:970
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 5:970:970
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p5:969:6:2:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "bufLen+0" a3 0
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t20 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t33 0 a4 p5:970:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,8=v8
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t20 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t33 0 a4 p5:970:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,8=v8
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t20 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t33 0 a4 p5:970:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,8=v8
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t20 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t33 0 a4 p5:970:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,8=v8
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v8 Const64 t2 8 - p0:0:0:0:0 1 -
v v9 Less64 t3 0 - p5:970:16:1:0 1 v8,v6
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 5:970:970
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v8,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{bytes.shouldUseASCIISet}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v5,v7,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
fstate scheduled,laidout
regalloc 11 v6:R0,v9:R0,v10:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v5,v7,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
fstate scheduled,laidout
regalloc 11 v6:R0,v9:R0,v10:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 10 1
b b1 Ret p5:970:18:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p5:970:18:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64CMPconst t29 8 - p5:970:16:1:0 1 v6
v v9 ARM64GreaterThan t3 0 - p5:970:16:1:0 1 v4
v v10 MakeResult t34 0 - p5:970:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v5,v7,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 5:970:970
fstate scheduled,laidout
regalloc 11 v6:R0,v9:R0,v10:[]
dcllen 2
end
frontend
end
ptrcache t2,t5,t6,t7,t8,t10,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t2,t14,t15,t25,t26,t12,t13,t3,t17,t18,t19,t20,t21,t22,t23,t33,t24,t1,t16,t27,t28,t30,t29,t31,t32,t34
eof
"#

/-- `std/std/bytes/shouldUseASCIISet,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "bytes"
func "shouldUseASCIISet" 1
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
name n1 "bufLen" PPARAM t1 1 "bytes.bufLen" 0 a3
type t2 1 1 0 0 - "bool"
name n2 "~r0" PPARAMOUT t2 1 "bytes.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p5 "bytes/bytes.go" 1 1 -1 3 "bytes/bytes.go" "bytes/bytes.go" 1 1
sym y1 "bytes.shouldUseASCIISet" 1
curfn p5:969:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 969 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "bytes.shouldUseASCIISet.arginfo1" 0
sym y4 "bytes.shouldUseASCIISet.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p5:969:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p5:969:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p5:969:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p5:969:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p5:969:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p5:969:6:2:0
p 6 6 0 0 0 - CMP 0 CONST/0/0/0/NONE/0/8/-/- 8192 - _ 0 0 p5:970:16:1:0
p 7 7 0 0 0 - CSET 0 SPECIAL/0/0/0/NONE/0/140/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p5:970:16:2:0
p 8 8 0 0 0 - RET 0 _ 0 - _ 0 0 p5:970:18:2:0
p 9 9 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 969 201080
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
dbgloc 0 1:-10000:1:9:50
dbgregout n2
dbgpc 1:9:8
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p5:969:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p5:969:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p5:969:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p5:969:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p5:969:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p5:969:6:2:0
p 6 0 0 0 96 - CMP 0 CONST/0/0/0/NONE/17/8/-/- 8192 - NONE/0/0/0/NONE/1/0/-/- 0 0 p5:970:16:1:0
p 7 4 0 0 103 - CSET 0 SPECIAL/0/0/0/NONE/11/140/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p5:970:16:2:0
p 8 8 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p5:970:18:2:0
fn y1 8 0 0 0 969 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 16 0 1f2000f1e0d79f9ac0035fd600000000 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 3
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 0 1 28000 - 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040400 0
data y9 SRODATA 3 1 28000 020400 0
data y10 SRODATA 3 1 28000 080400 0
data y11 SRODATA 4 1 28000 960f0400 0
data y12 SRODATA 3 1 28000 000400 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "go:info.bytes.shouldUseASCIISet$abstract" 0
sym y17 "" 0
sym y18 "go:info.int" 0
sym y19 "go:info.bool" 0
sym y20 "type:bool" 0
dwfn y13 y14 y15 y16 y17 "bytes.shouldUseASCIISet" 3:969 1 0 1 136
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y16 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "int" 0 0 1 p5:969:24:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "bool" 0 0 1 p5:969:36:0:0
var 0 0 "bufLen" 5 1 0 0 0 8 y18 "bytes/bytes.go" 969 24 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y19 "bytes/bytes.go" 969 36 0 1 0 0 -
scope 0 0 - 0,1
dieref y13 3 y16 0
dieoff y16 0:29
data y13 SDWARFFCN 33 0 0 0600000000000010019c2900000000000000002e7e72300001c907000000000000 6
reloc 0 0 R_USETYPE 0 y20
reloc 1 4 R_DWARFSECREF 0 y16
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y16
reloc 15 4 R_DWARFSECREF 0 y14
reloc 27 4 R_DWARFSECREF 0 y19
data y14 SDWARFLOC 9 0 0 010000040008015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 24 0 0 0009020000000000000000040403c407140637020c000101 1
reloc 3 8 R_ADDR 0 y1
data y16 SDWARFABSFCN 43 0 1 0562797465732e73686f756c6455736541534349495365740001c90701226275664c656e00000000000000 1
reloc 38 4 R_DWARFSECREF 0 y18
end
eof
"#

/-- The loaded `bytes.shouldUseASCIISet` (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG23` gives (`b1`: the no-code `v6`, `v1`; `v4`'s `PCDATA` and `CMP`;
`v9`'s `CSET`; the no-code `v10`; `RET`). -/
def tab : PcTab := [(1, [5, 5, 5, 7, 8, 8])]

/-- The class table `checkG23` gives (`R0` at class 64 at the entry). -/
def kt : KTab := (match checkG23 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG23`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The empty memory. -/
def mem0 : Mem := {}

/-- The `runLoc` state before `v4`: `len(chars) = 10` in `R0`, every other register `poison`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w64 10 else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v4`: `X0 = 10`, the activation's `g` and `FP`, the PC of `v4`, a zero
memory. -/
def m0 : MState :=
  { x := fun k => if k = 0 then 10 else if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8
      else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := fun _ => 0 }

/-- A read that gives no pointer. -/
def noPtr (r : Res Val) : Bool :=
  match r with
  | .ok (.ptr _) => false
  | _ => true

/-- The register holds the boolean `true`. -/
def isTrue : Option Val → Bool
  | some (.bool true) => true
  | _ => false

theorem isTrue_spec {o : Option Val} (h : isTrue o = true) : o = some (.bool true) := by
  unfold isTrue at h
  split at h
  · rfl
  · cases h

/-- What compiled evaluation checks on `shouldUseASCIISet`: `checkG23` accepts it with `tab` and
`kt` and `checkG22` does not; it accesses no frame variable and has no home slot; `b1` holds `v4`
(`CMPconst`, whose arguments read no pointer in `s0`) at index 2 and `v9` (`GreaterThan`) at index
3, `R0` has class 64 before `v4` and nothing is in the upper-bit table there; `stepLoc` runs `v4`
and then `v9` from `s0` to `R0 = true`. -/
def gFacts : Bool :=
  (checkG23 lc ps bs g).toOption == some (tab, kt) && (checkG22 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 4).isSome && (lc.ctx.f.value? 9).isSome &&
    blk1.values[2]? == some 4 && blk1.values[3]? == some 9 &&
    (val 4).op == .ARM64CMPconst && (val 9).op == .ARM64GreaterThan &&
    (val 4).args.toList.all (fun a => noPtr (s0.read lc a)) &&
    (kAt lc kt 1 blk1 2).get 0 == some 64 && uAt lc blk1 2 == none &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 4)) (fun s1 =>
      GenG1.okThen (stepLoc GenG2.env lc s1 (val 9)) fun s2 => isTrue s2.regs[0]?)

theorem g23_facts : gFacts = true := by
  native_decide

/-- The facts of `g23_facts` as hypotheses. -/
theorem facts :
    checkG23 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 1 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 1 = some blk1 ∧ lc.ctx.f.value? 4 = some (val 4) ∧
      lc.ctx.f.value? 9 = some (val 9) ∧ blk1.values[2]? = some 4 ∧ blk1.values[3]? = some 9 ∧
      (val 4).op = .ARM64CMPconst ∧ (val 9).op = .ARM64GreaterThan ∧
      (∀ a ∈ (val 4).args.toList, noPtr (s0.read lc a) = true) ∧
      (kAt lc kt 1 blk1 2).get 0 = some 64 ∧ uAt lc blk1 2 = none ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 4)) (fun s1 =>
        GenG1.okThen (stepLoc GenG2.env lc s1 (val 9)) fun s2 => isTrue s2.regs[0]?) = true := by
  have hf := g23_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.all_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hm1⟩, hb1s⟩, hv4s⟩, hv9s⟩, hi2⟩, hi3⟩, hop4⟩,
    hop9⟩, hargs⟩, hk0⟩, hu⟩, hrun⟩ := hf
  refine ⟨?_, hav, hsl, hm1, ?_, ?_, ?_, hi2, hi3, hop4, hop9, hargs, hk0, hu, hrun⟩
  · revert hres; cases checkG23 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [blk1, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv4s
    simp [val, hv]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv9s
    simp [val, hv]

theorem g23Env (hc : checkG23 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG23_spec hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := GenG12.addrAgree
        glob := fun _ _ _ _ => rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG23_spec hc
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
    (r = 0 ∧ x = .int .w64 10) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
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

theorem g23Inv0 (h0 : (kAt lc kt 1 blk1 2).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk1 2) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v4`, the compare: its arguments read no pointer; it is no load,
subtraction, pair load, nil check, zeroing or register-index load. -/
theorem pre4 (hop : (val 4).op = .ARM64CMPconst)
    (hargs : ∀ a ∈ (val 4).args.toList, noPtr (s0.read lc a) = true) : G14Pre lc s0 (val 4) := by
  have hne : ∀ o : Op, o ≠ .ARM64CMPconst → (val 4).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro _ a ha x hx p hp
    have := hargs a ha
    rw [hx, hp] at this
    cases this
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- The per-value premises of `v9`, `GreaterThan`: none apply. -/
theorem pre9 {s : LocState} (hop : (val 9).op = .ARM64GreaterThan) : G14Pre lc s (val 9) := by
  have hne : ∀ o : Op, o ≠ .ARM64GreaterThan → (val 9).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G23 on `bytes.shouldUseASCIISet`**: from the state before `v4` with `len(chars) = 10` in
`R0` (`X0 = 10`), `g23_value` runs `CMP $8, R0` (`v4`), and then `GreaterThan` (`v9`, `CSET GT,
R0`) on the flags `LocMatch` relates to `NZCV`: `runLoc`'s `R0` holds `true` and the machine
state, related to it before `v10` under an activation extending `E`, has `X0 = 1`. -/
theorem genG23_value_witness :
    ∃ s1 s2 E1 m1 E2 m2, stepLoc GenG2.env lc s0 (val 4) = .ok s1 ∧
      stepLoc GenG2.env lc s1 (val 9) = .ok s2 ∧ s2.regs[0]? = some (.bool true) ∧
      E.Extends E1 ∧ E1.Extends E2 ∧ G10Env lc g L ps 0 tab E2 ∧
      PStar GenG2.H0 L ps.toList 0 m0 m1 ∧ LocMatch E1 s1 1 3 m1 ∧
      PStar GenG2.H0 L ps.toList 0 m1 m2 ∧ LocMatch E2 s2 1 4 m2 ∧ m2.x 0 = 1 := by
  obtain ⟨hc, hav, hsl, hm1, hb, hv4, hv9, hi2, hi3, hop4, hop9, hargs, hk0, hu, hrun⟩ := facts
  obtain ⟨s1, hs1, h2⟩ := GenG1.okThen_spec hrun
  obtain ⟨s2, hs2, hr2⟩ := GenG1.okThen_spec h2
  have hr2' := isTrue_spec hr2
  have hE := g23Env hc hav hsl
  have hne4 : ∀ o : Op, o ≠ .ARM64CMPconst → (val 4).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop4)
  have hne9 : ∀ o : Op, o ≠ .ARM64GreaterThan → (val 9).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop9)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', hinv1, hu1⟩ := g23_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm1 hb hi2 hv4 (by rw [hop4]; rfl) locMatch0 (g23Inv0 hk0) (by rw [hu]; trivial)
    (pre4 hop4 hargs)
    (fun h => absurd h (hne4 _ (by decide))) (fun h => absurd h (hne4 _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop4]; rfl))
    (fun h => absurd h (hne4 _ (by decide))) (fun h => absurd h (hne4 _ (by decide)))
    (fun h => absurd h (hne4 _ (by decide))) hs1
  obtain ⟨E2, m2, hx2, hE2, hp2, hm2', -, -⟩ := g23_value (H := GenG2.H0) (env := GenG2.env)
    hc hE1 hm1 hb hi3 hv9 (by rw [hop9]; rfl) hm1' hinv1 hu1 (pre9 hop9)
    (fun h => absurd h (hne9 _ (by decide))) (fun h => absurd h (hne9 _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop9]; rfl))
    (fun h => absurd h (hne9 _ (by decide))) (fun h => absurd h (hne9 _ (by decide)))
    (fun h => absurd h (hne9 _ (by decide))) hs2
  exact ⟨s1, s2, E1, m1, E2, m2, hs1, hs2, hr2', hx1, hx2, hE2, hp1, hm1', hp2, hm2',
    (hm2'.regs 0 _ hr2').1 0 rfl⟩

end GoFV.Proof.Witness.GenG23
