import GoFV.Proof.Gen.G30
import GoFV.Proof.Witness.GenG26
import GoFV.Proof.Witness.GenG29

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G30 of the genssa validator on `runtime.gclinkptr.ptr`

`std/std/runtime/gclinkptr.ptr,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`):

```go
func (p gclinkptr) ptr() *gclink { return (*gclink)(unsafe.Pointer(p)) }
```

Its trimmed body holds no arm64 op: `v6 = ArgIntReg` (in `R0`), `InitMem`, `v8 = Convert v6 v1`
(in `R0`), `MakeResult`, a `Ret` block. So `runLoc` runs it in Phase 1's mode, and `checkG29`
rejects it (`v8: op Convert in a function with no arm64 op`). `checkG30` accepts it with the PC
table `tab` and the class table `kt`. genssa emits no code for the `Convert`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g30_facts`),
`stepLoc` runs `v8` from a state with `p = 0x1234` in `R0`, and `R0` then holds `0x1234`. On a
framed activation with `G28Env` (as `GenG26`'s) with `X0 = 0x1234`, `g30_value` runs `v8`: the
machine's `X0` is `0x1234` (`genG30_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG30

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/gclinkptr.ptr,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "gclinkptr.ptr" 1 0 0
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
type t2 UINTPTR 8 8 0 comparable,named "gclinkptr" "runtime.gclinkptr"
type t4 STRUCT 8 8 0 comparable,named "gclink" "runtime.gclink" 1
field 0 "next" t2 0 0
type t3 PTR 8 8 8 hasptr,direct,comparable "*gclink" "*runtime.gclink" t4
type t1 FUNC 8 8 8 hasptr,direct "method(gclinkptr) func() *gclink" "method(runtime.gclinkptr) func() *runtime.gclink" 1 0 1
field 0 "p" t2 ? 0
field 1 "" t3 ? 0
aux a2 sym "runtime.gclinkptr.ptr" "runtime.gclinkptr.ptr" 1 - 0 - - - - 0
posbase p47 "runtime/mcache.go" 1 1 -1
aux a3 name "p" "p" PPARAM t2 0 1 used p47:85:7:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t3 0 1 - p47:85:26:0:0
aux a1 call "AuxCall{runtime.gclinkptr.ptr}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
type t5 BOOL 1 1 0 comparable,named "bool" "bool"
type t6 INT8 1 1 0 comparable,named "int8" "int8"
type t7 INT16 2 2 0 comparable,named "int16" "int16"
type t8 INT32 4 4 0 comparable,named "int32" "int32"
type t9 INT64 8 8 0 comparable,named "int64" "int64"
type t10 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t11 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t12 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t13 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t14 INT 8 8 0 comparable,named "int" "int"
type t15 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t16 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t17 UINT 8 8 0 comparable,named "uint" "uint"
type t18 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t19 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t10
type t21 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t8
type t22 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t12
type t23 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t14
type t24 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t18
type t25 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t15
type t26 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t16
type t27 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t20
type t28 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t29 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t30 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t31 SSA ? ? ? - "mem" ""
type t32 SSA ? ? ? - "flags" ""
type t33 SSA ? ? ? - "void" ""
type t34 SSA 16 8 ? - "int128" ""
type t35 RESULTS ? ? ? - "mem" "" 1 t31
type t36 PTR 8 8 8 hasptr,direct,comparable "*gclinkptr" "*runtime.gclinkptr" t2
type t37 PTR 8 8 8 hasptr,direct,comparable "**gclink" "**runtime.gclink" t3
type t38 RESULTS ? ? ? - "*gclink,mem" "" 2 t3,t31
slot s1 a3 t2 0 - 0
f b1 t1 a1 10 1
typs Bool=t5,Int8=t6,Int16=t7,Int32=t8,Int64=t9,UInt8=t10,UInt16=t11,UInt32=t12,UInt64=t13,Int=t14,Float32=t15,Float64=t16,UInt=t17,Uintptr=t18,String=t19,BytePtr=t20,Int32Ptr=t21,UInt32Ptr=t22,IntPtr=t23,UintptrPtr=t24,Float32Ptr=t25,Float64Ptr=t26,BytePtrPtr=t27,Complex64=t28,Complex128=t29,UnsafePtr=t30,Mem=t31,Flags=t32,Void=t33,Int128=t34,ResultMem=t35
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t37 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v7 ConstNil t3 0 - p0:0:0:0:0 0 -
v v8 Convert t30 0 - p47:86:34:0:0 1 v6,v1
v v9 Copy t3 0 - p47:86:33:2:0 1 v8
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 3344556677=v7
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t37 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v7 ConstNil t3 0 - p0:0:0:0:0 0 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v9 Copy t3 0 - p47:86:33:2:0 1 v8
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 3344556677=v7
freev -
freeb -
cache postorder b1
cache linestarts 47:86:86
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t37 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v7 ConstNil t3 0 - p0:0:0:0:0 0 -
v v8 Convert t30 0 - p47:86:34:1:0 2 v6,v1
v v9 Copy t3 0 - p47:86:33:2:0 0 v8
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 3344556677=v7
freev -
freeb -
cache postorder b1
cache linestarts 47:86:86
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 47:86:86
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 47:86:86
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 47:86:86
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 47:86:86
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 47:86:86
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 47:86:86
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 47:86:86
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p47:85:6:2:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "p+0" a3 0
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
v v9 SB t18 0 - p0:0:0:0:0 0 -
v v7 SP t18 0 - p0:0:0:0:0 2 -
v v5 OffPtr t36 0 - p0:0:0:0:0 0 v7
v v4 LocalAddr t37 0 a4 p47:86:2:0:0 0 v7,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v5
freev v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
v v9 SB t18 0 - p0:0:0:0:0 0 -
v v7 SP t18 0 - p0:0:0:0:0 2 -
v v5 OffPtr t36 0 - p0:0:0:0:0 0 v7
v v4 LocalAddr t37 0 a4 p47:86:2:0:0 0 v7,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v5
freev v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
v v9 SB t18 0 - p0:0:0:0:0 0 -
v v7 SP t18 0 - p0:0:0:0:0 2 -
v v5 OffPtr t36 0 - p0:0:0:0:0 0 v7
v v4 LocalAddr t37 0 a4 p47:86:2:0:0 0 v7,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v5
freev v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
v v9 SB t18 0 - p0:0:0:0:0 0 -
v v7 SP t18 0 - p0:0:0:0:0 2 -
v v5 OffPtr t36 0 - p0:0:0:0:0 0 v7
v v4 LocalAddr t37 0 a4 p47:86:2:0:0 0 v7,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v5
freev v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 47:86:86
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v5,v7,v9,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.gclinkptr.ptr}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
fstate scheduled,laidout
regalloc 11 v6:R0,v8:R0,v10:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
fstate scheduled,laidout
regalloc 11 v6:R0,v8:R0,v10:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 10 1
b b1 Ret p47:86:34:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p47:86:34:1:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v8 Convert t30 0 - p47:86:34:1:0 1 v6,v1
v v10 MakeResult t38 0 - p47:86:2:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 47:86:86
fstate scheduled,laidout
regalloc 11 v6:R0,v8:R0,v10:[]
dcllen 2
end
frontend
end
ptrcache t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t24,t27,t28,t29,t30
typelink t31=t35
typeorder t6,t10,t7,t11,t8,t12,t9,t13,t14,t17,t18,t2,t28,t29,t15,t16,t5,t20,t21,t22,t23,t24,t36,t25,t26,t27,t37,t3,t1,t4,t19,t30,t31,t33,t32,t34,t35,t38
eof
"#

/-- `std/std/runtime/gclinkptr.ptr,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "gclinkptr.ptr" 1
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
type t1 8 8 0 0 - "gclinkptr"
name n1 "p" PPARAM t1 1 "runtime.p" 0 a3
type t2 8 8 8 1 01 "*gclink"
name n2 "~r0" PPARAMOUT t2 1 "runtime.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p47 "runtime/mcache.go" 1 1 -1 46 "runtime/mcache.go" "runtime/mcache.go" 1 1
sym y1 "runtime.gclinkptr.ptr" 1
curfn p47:85:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 85 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.gclinkptr.ptr.arginfo1" 0
sym y4 "runtime.gclinkptr.ptr.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p47:85:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p47:85:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p47:85:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p47:85:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p47:85:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p47:85:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p47:86:34:1:0
p 7 7 0 0 0 - RET 0 _ 0 - _ 0 0 p47:86:34:1:0
p 8 8 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 85 201080
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
dbgloc 0 1:-10000:1:10:50
dbgregout n2
dbgpc 1:10:6
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p47:85:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p47:85:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p47:85:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p47:85:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p47:85:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p47:85:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p47:86:34:1:0
p 7 0 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p47:86:34:1:0
fn y1 8 0 0 0 85 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 16 0 c0035fd6000000000000000000000000 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 46
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 3 1 28000 010400 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040400 0
data y9 SRODATA 3 1 28000 020400 0
data y10 SRODATA 3 1 28000 5e0400 0
data y11 SRODATA 4 1 28000 ae010400 0
data y12 SRODATA 3 1 28000 000400 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "go:info.runtime.gclinkptr.ptr$abstract" 0
sym y17 "" 0
sym y18 "go:info.runtime.gclinkptr" 0
sym y19 "go:info.*runtime.gclink" 0
sym y20 "type:*runtime.gclink" 0
dwfn y13 y14 y15 y16 y17 "runtime.gclinkptr.ptr" 46:85 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y16 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "runtime.gclinkptr" 0 0 1 p47:85:7:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "*runtime.gclink" 0 0 1 p47:85:26:0:0
var 0 0 "p" 5 1 0 0 0 8 y18 "runtime/mcache.go" 85 7 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y19 "runtime/mcache.go" 85 26 0 1 0 0 -
scope 0 0 - 0,1
dieref y13 3 y16 0
dieoff y16 0:26
data y13 SDWARFFCN 32 0 0 0600000000000010019c2900000000000000002e7e7230000155000000000000 6
reloc 0 0 R_USETYPE 0 y20
reloc 1 4 R_DWARFSECREF 0 y16
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y16
reloc 15 4 R_DWARFSECREF 0 y14
reloc 26 4 R_DWARFSECREF 0 y19
data y14 SDWARFLOC 9 0 0 010000040000015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 22 0 0 0009020000000000000000042f03d000140210000101 1
reloc 3 8 R_ADDR 0 y1
data y16 SDWARFABSFCN 35 0 1 0572756e74696d652e67636c696e6b7074722e70747200015501227000000000000000 1
reloc 30 4 R_DWARFSECREF 0 y18
end
eof
"#

/-- The loaded method (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG30` gives (`b1`: one entry per value `v6`, `v1`, `v8`, `v10`, then the
`RET`). -/
def tab : PcTab := [(1, [5, 5, 5, 5, 5])]

/-- The class table `checkG30` gives. -/
def kt : KTab := (match checkG30 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG30`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `runLoc` state before `v8`: the receiver `p = 0x1234` in `R0`, every other register
`poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG26.mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w64 0x1234 else .poison,
    flags := .poison, slots := [], mem := .mem GenG26.mem0 }

/-- The machine before `v8`: `X0 = 0x1234`, the activation's `g` and `FP`, the PC of `v8`, a zero
memory. -/
def m0 : MState :=
  { x := fun k => if k = 0 then 0x1234 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := fun _ => 0 }

/-- The register holds the 64-bit integer `0x1234`. -/
def isP : Option Val → Bool
  | some (.int .w64 x) => x == 0x1234
  | _ => false

theorem isP_spec {o : Option Val} (h : isP o = true) : o = some (.int .w64 0x1234) := by
  unfold isP at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on the method: it holds no arm64 op, `checkG30` accepts it
with `tab` and `kt` and `checkG29` does not; it accesses no frame variable and has no home slot;
`b1` holds `v8` (`Convert`) at index 2, `R0` has class 64 before `v8` and the upper-bit table is
empty there; `stepLoc` runs `v8` from `s0` to `R0 = 0x1234`. -/
def gFacts : Bool :=
  !lc.ctx.f.lowered &&
    (checkG30 lc ps bs g).toOption == some (tab, kt) && (checkG29 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 8).isSome && blk1.values[2]? == some 8 && (val 8).op == .Convert &&
    (kAt lc kt 1 blk1 2).get 0 == some 64 && uL lc blk1 2 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 8)) fun s1 => isP s1.regs[0]?

theorem g30_facts : gFacts = true := by
  native_decide

/-- The facts of `g30_facts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = false ∧ checkG30 lc ps bs g = .ok (tab, kt) ∧
      (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 1 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 1 = some blk1 ∧ lc.ctx.f.value? 8 = some (val 8) ∧
      blk1.values[2]? = some 8 ∧ (val 8).op = .Convert ∧
      (kAt lc kt 1 blk1 2).get 0 = some 64 ∧ uL lc blk1 2 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 8)) (fun s1 => isP s1.regs[0]?) = true := by
  have hf := g30_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, Bool.not_eq_true'] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hres⟩, -⟩, hav⟩, hsl⟩, hm1⟩, hb1s⟩, hv8s⟩, hi2⟩, hop⟩, hk0⟩, hu⟩,
    hrun⟩ := hf
  refine ⟨hl, ?_, hav, hsl, hm1, ?_, ?_, hi2, hop, hk0, hu, hrun⟩
  · revert hres; cases checkG30 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [blk1, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv8s
    simp [val, hv]

theorem g30Env (hc : checkG30 lc ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = false)
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
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ :=
              checkNL30_spec (checkG30_nl hl hc)
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ :=
              checkNL30_spec (checkG30_nl hl hc)
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

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w64 0x1234) ∨ x = .poison := by
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
  mem := ⟨GenG26.mem0, rfl, GenG26.memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g30Inv0 (h0 : (kAt lc kt 1 blk1 2).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk1 2) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG26.mem0, rfl, by simp [KeysNodup, GenG26.mem0],
      fun b al a h => by simp [GenG26.mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v8`, the `Convert`: none apply. -/
theorem pre8 {s : LocState} (hop : (val 8).op = .Convert) : G14Pre lc s (val 8) := by
  have hne : ∀ o : Op, o ≠ .Convert → (val 8).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G30 on `runtime.gclinkptr.ptr`**: from the state before `v8` with `p = 0x1234` in `R0`
(`X0 = 0x1234`), `g30_value` runs the `Convert` (`v8`, no code) in Phase 1's mode: `runLoc`'s
`R0` holds `0x1234` and the machine state, related to it before `v10` under an activation
extending `E` that is again a `G28Env`, has `X0 = 0x1234`. -/
theorem genG30_value_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 8) = .ok s1 ∧ s1.regs[0]? = some (.int .w64 0x1234) ∧
      E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E1 s1 1 3 m1 ∧ m1.x 0 = 0x1234 := by
  obtain ⟨hl, hc, hav, hsl, hm1, hb, hv8, hi2, hop, hk0, hu, hrun⟩ := facts
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hr1' := isP_spec hr1
  have hE := g30Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .Convert → (val 8).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g30_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm1 hb hi2 hv8 (by rw [hop]; rfl) locMatch0 (g30Inv0 hk0)
    (by rw [hu]; intro e he; cases he) (pre8 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  exact ⟨s1, E1, m1, hs1, hr1', hx1, hE1, hp1, hm1',
    valRel_i64 hA ((hm1'.regs 0 _ hr1').1 0 rfl)⟩

end GoFV.Proof.Witness.GenG30
