import GoFV.Proof.Gen.G38
import GoFV.Proof.Witness.GenG14

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G38 of the genssa validator on `sync/atomic.LoadInt64`

`std/std/sync/atomic/LoadInt64,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`;
`sync/atomic/doc.go`, implemented in `internal/runtime/atomic`):

```go
func LoadInt64(addr *int64) (val int64)
```

Block `b1` (the entry): `v6 = ArgIntReg` (`addr`, `R0`), `InitMem`, `v8 = LDAR v6 v1` (`LDAR (R0),
R0`, homed in `(R0;-)`), `v10 = Select0 v8` (`R0`), `v9 = Select1 v8` (the memory), `MakeResult`.
G37 has no acquire load, so `checkG37` rejects the function (`op LDAR`, `select of LDAR`);
`checkG38` accepts it with the PC table `tab` and the class table `kt`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g38_facts`),
`stepLoc` runs `v8` from a state with `addr` the pointer to offset 16 of the heap object `heap 1`
of `GenG14` (`mem7`: the word 7 there) in `R0` to `R0 = 7`. On a framed activation with `G28Env`
(`heap 1` injected at `2^41`, the machine memory `M7`), `g38_value` runs `LDAR (R0), R0`
(`genG38_witness`): `LdarPre` holds (the 8 bytes at the address are valid), and the machine's
`X0` is 7.
-/

namespace GoFV.Proof.Witness.GenG38

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/sync/atomic/LoadInt64,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "sync/atomic"
func "LoadInt64" 1 1 0
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
config localpkg "sync/atomic"
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
type t3 INT64 8 8 0 comparable,named "int64" "int64"
type t2 PTR 8 8 8 hasptr,direct,comparable "*int64" "*int64" t3
type t1 FUNC 8 8 8 hasptr,direct "func(*int64) int64" "func(*int64) int64" 0 1 1
field 0 "addr" t2 ? 0
field 1 "val" t3 ? 0
aux a2 sym "sync/atomic.LoadInt64" "sync/atomic.LoadInt64" 1 - 0 - - - - 0
posbase p4 "sync/atomic/doc_64.go" 1 1 -1
aux a3 name "addr" "addr" PPARAM t2 0 1 used p4:86:16:0:0
aux a4 name "val" "val" PPARAMOUT t3 0 1 - p4:86:30:0:0
aux a1 call "AuxCall{sync/atomic.LoadInt64}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
type t4 BOOL 1 1 0 comparable,named "bool" "bool"
type t5 INT8 1 1 0 comparable,named "int8" "int8"
type t6 INT16 2 2 0 comparable,named "int16" "int16"
type t7 INT32 4 4 0 comparable,named "int32" "int32"
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
type t19 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t7
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t21 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t12
type t22 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t16
type t23 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t13
type t24 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t14
type t25 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t18
type t26 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t27 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t28 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t29 SSA ? ? ? - "mem" ""
type t30 SSA ? ? ? - "flags" ""
type t31 SSA ? ? ? - "void" ""
type t32 SSA 16 8 ? - "int128" ""
type t33 RESULTS ? ? ? - "mem" "" 1 t29
posbase p1 "<autogenerated>" 1 1 -1
type t34 PTR 8 8 8 hasptr,direct,comparable "**int64" "**int64" t2
type t35 TUPLE ? ? ? - "uint64,mem" "" t11 t29
type t36 RESULTS ? ? ? - "int64,mem" "" 2 t3,t29
slot s1 a3 t2 0 - 0
f b1 t1 a1 11 1
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t3,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t14,UInt=t15,Uintptr=t16,String=t17,BytePtr=t18,Int32Ptr=t19,UInt32Ptr=t20,IntPtr=t21,UintptrPtr=t22,Float32Ptr=t23,Float64Ptr=t24,BytePtrPtr=t25,Complex64=t26,Complex128=t27,UnsafePtr=t28,Mem=t29,Flags=t30,Void=t31,Int128=t32,ResultMem=t33
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t2 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t3 0 - p0:0:0:0:0 0 -
v v8 AtomicLoad64 t35 0 - p1:1:0:0:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t2 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t3 0 - p0:0:0:0:0 0 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t2 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t3 0 - p0:0:0:0:0 0 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 20 "expand calls"
aux a5 nameoff "addr+0" a3 0
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 2 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
v v7 SB t16 0 - p0:0:0:0:0 0 -
v v5 SP t16 0 - p0:0:0:0:0 2 -
v v4 OffPtr t34 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t2 0 a4 p1:1:0:0:0 0 v5,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 21 "decompose builtin"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 2 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
v v7 SB t16 0 - p0:0:0:0:0 0 -
v v5 SP t16 0 - p0:0:0:0:0 2 -
v v4 OffPtr t34 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t2 0 a4 p1:1:0:0:0 0 v5,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 2 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
v v7 SB t16 0 - p0:0:0:0:0 0 -
v v5 SP t16 0 - p0:0:0:0:0 2 -
v v4 OffPtr t34 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t2 0 a4 p1:1:0:0:0 0 v5,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 2 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
v v7 SB t16 0 - p0:0:0:0:0 0 -
v v5 SP t16 0 - p0:0:0:0:0 2 -
v v4 OffPtr t34 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t2 0 a4 p1:1:0:0:0 0 v5,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 AtomicLoad64 t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 33 "lower"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 36 "pair"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a1 call "AuxCall{sync/atomic.LoadInt64}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 12 v6:R0,v8:(R0;-),v10:R0,v11:[]
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 12 v6:R0,v8:(R0;-),v10:R0,v11:[]
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 11 1
b b1 Ret p1:1:0:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p1:1:0:1:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v8 ARM64LDAR t35 0 - p1:1:0:1:0 2 v6,v1
v v10 Select0 t11 0 - p1:1:0:0:0 1 v8
v v9 Select1 t29 0 - p1:1:0:0:0 1 v8
v v11 MakeResult t36 0 - p1:1:0:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 12 v6:R0,v8:(R0;-),v10:R0,v11:[]
dcllen 3
end
frontend
end
ptrcache t3,t6,t7,t8,t10,t11,t12,t13,t14,t16,t17,t18,t25,t28
typelink t29=t33
typeorder t5,t8,t6,t9,t7,t10,t3,t11,t12,t15,t16,t26,t27,t13,t14,t4,t18,t19,t20,t2,t21,t22,t23,t24,t25,t34,t1,t17,t28,t29,t31,t30,t32,t35,t33,t36
eof
"#

/-- `std/std/sync/atomic/LoadInt64,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "sync/atomic"
func "LoadInt64" 1
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
type t1 8 8 8 1 01 "*int64"
name n1 "addr" PPARAM t1 1 "sync/atomic.addr" 0 a3
type t2 8 8 0 0 - "int64"
name n2 "val" PPARAMOUT t2 1 "sync/atomic.val" 0 a4
name n3 ".autotmp_2" PAUTO t2 3 "sync/atomic..autotmp_2" 0 -
in n1 0 used
in n2 0 outregs
in n3 0 used,autotmp
out n1 0 used
opt n3 0 autotmp
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p1 "<autogenerated>" 1 1 -1 0 "<autogenerated>" "<autogenerated>" 1 1
sym y1 "sync/atomic.LoadInt64" 1
curfn p1:1:0:0:0 0 0
regargs 8192:0:t1
text y1 0 0 23 0 1 210085
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "sync/atomic.LoadInt64.arginfo1" 0
sym y5 "sync/atomic.LoadInt64.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p1:1:0:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p1:1:0:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p1:1:0:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p1:1:0:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p1:1:0:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p1:1:0:1:0
p 7 7 0 0 0 - LDAR 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p1:1:0:1:0
p 8 8 0 0 0 - RET 0 _ 0 - _ 0 0 p1:1:0:2:0
p 9 9 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 23 0 1 210085
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:1:11:50
dbgregout n2
dbgpc 1:11:8
end
asm
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p1:1:0:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p1:1:0:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p1:1:0:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p1:1:0:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p1:1:0:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p1:1:0:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:1:0
p 7 0 0 0 233 - LDAR 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 8 4 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p1:1:0:2:0
fn y1 8 0 23 0 1 2100cd
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 16 0 00fcdfc8c0035fd60000000000000000 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y3,_,_,_,y4,y5
usedfiles 0
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y6 SRODATA 3 1 28000 010400 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 040400 0
data y10 SRODATA 3 1 28000 020400 0
data y11 SRODATA 3 1 28000 020400 0
data y12 SRODATA 3 1 28000 040400 0
data y13 SRODATA 3 1 28000 000400 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
posbase p4 "sync/atomic/doc_64.go" 1 1 -1 3 "sync/atomic/doc_64.go" "sync/atomic/doc_64.go" 1 1
sym y18 "go:info.*int64" 0
sym y19 "go:info.int64" 0
sym y20 "type:int64" 0
dwfn y14 y15 y16 - y17 "sync/atomic.LoadInt64" 0:1 1 0 1 127
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "*int64" 0 0 1 p4:86:16:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "int64" 0 0 1 p1:1:0:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "int64" 0 0 1 p4:86:30:0:0
var 0 0 "addr" 5 1 0 0 0 8 y18 "sync/atomic/doc_64.go" 86 16 0 0 0 0 v0
var 1 0 "val" 5 1 1 0 0 0 y19 "sync/atomic/doc_64.go" 86 30 0 1 0 0 -
scope 0 0 - 0,1
data y14 SDWARFFCN 63 0 0 0373796e632f61746f6d69632e4c6f6164496e74363400000010019c0100000001012d6164647200005600000000000000002e76616c000156000000000000 5
reloc 0 0 R_USETYPE 0 y20
reloc 23 2 R_DWTXTADDR_U2 0 y1
reloc 42 4 R_DWARFSECREF 0 y18
reloc 46 4 R_DWARFSECREF 0 y15
reloc 57 4 R_DWARFSECREF 0 y19
data y15 SDWARFLOC 9 0 0 010000040004015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 18 0 0 00090200000000000000000637020c000101 1
reloc 3 8 R_ADDR 0 y1
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

/-- The PC table `checkG38` gives. -/
def tab : PcTab := (match checkG38 lc ps bs g with
  | .ok (t, _) => t
  | .error _ => [])

/-- The class table `checkG38` gives. -/
def kt : KTab := (match checkG38 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `2^41` (`GenG14.ι`) and the PC table of `checkG38`. -/
def E : MatchEnv :=
  { lc, ι := GenG14.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `runLoc` state before `v8`: `addr` the pointer to offset 16 of `heap 1` (`GenG14.pQ`) in
`R0`, every other register `poison`, the memory `GenG14.mem7` (the word 7 there). -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG14.mem7 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .ptr GenG14.pQ else .poison,
    flags := .poison, slots := [], mem := .mem GenG14.mem7 }

/-- The machine before `v8`: `X0` the address `2^41 + 16`, the activation's `g` and `FP`, the PC of
`v8`, the memory `GenG14.M7`. -/
def m0 : MState :=
  { x := fun k => if k = 0 then GenG14.A + 16 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := GenG14.M7 }

/-- `v8`'s address in `s0`: its argument `v6` read as a base whose address at offset 0 is
`GenG14.pQ`. -/
def addrIsQ (s : LocState) : Bool :=
  GenG1.okThen (s.read lc 6) fun x => Arm64.addr x 0 == some GenG14.pQ

theorem addrIsQ_spec {s : LocState} (h : addrIsQ s = true) :
    ∃ x, s.read lc 6 = .ok x ∧ Arm64.addr x 0 = some GenG14.pQ := by
  obtain ⟨x, hx, h1⟩ := GenG1.okThen_spec h
  exact ⟨x, hx, by simpa using h1⟩

/-- What compiled evaluation checks on `LoadInt64`: it holds an arm64 op, `checkG38` accepts it
with `tab` and `kt` and `checkG37` does not; it accesses no frame variable and has no home slot;
`b1` is the entry and holds `v8` (`LDAR v6 v1`) at index 2, where `R0` has class 64 and G35's
table is empty; in `s0` its address is `GenG14.pQ`, where `mem7` has 8 readable bytes; `stepLoc`
runs `v8` from `s0` and `R0` then holds 7, which `Ptr.ofAddr` reads as no block's address. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG38 lc ps bs g).toOption == some (tab, kt) && (checkG37 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 8).isSome && blk.values[2]? == some 8 &&
    (val 8).op == .ARM64LDAR && (val 8).args[0]? == some 6 &&
    (kAt lc kt 1 blk 2).get 0 == some 64 &&
    uL35 lc (uIn35 lc 1) blk 2 == [] &&
    addrIsQ s0 && (GenG14.mem7.read GenG14.pQ 8).isSome &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 8)) GenG14.r0Is7 && (Ptr.ofAddr 7).blk == .nil

theorem g38_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG38 lc ps bs g = .ok (tab, kt) ∧
      (checkG37 lc ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 8 = some (val 8) ∧ blk.values[2]? = some 8 ∧
      (val 8).op = .ARM64LDAR ∧ (val 8).args[0]? = some 6 ∧
      (kAt lc kt 1 blk 2).get 0 = some 64 ∧
      uL35 lc (uIn35 lc 1) blk 2 = [] ∧ addrIsQ s0 = true ∧
      (GenG14.mem7.read GenG14.pQ 8).isSome = true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 8)) GenG14.r0Is7 = true ∧
      (Ptr.ofAddr 7).blk = .nil := by
  have hf := g38_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h37, hav, hsl, hm1, hbs, hvs, hi2, hop, ha0, hk0, hu2, hq, hrd, hrun, h7⟩ := hf
  refine ⟨hl, ?_, h37, hav, hsl, hm1, ?_, ?_, hi2, hop, ha0, hk0, hu2, hq, hrd, hrun, h7⟩
  · revert hres; cases checkG38 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g38Env (hc : checkG38 lc ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ := checkG38_spec hl hc
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ := checkG38_spec hl hc
            intro y
            have hs : L.sym y = GenG2.symA := rfl
            rw [hs]
            refine ⟨by decide, fun p hp => ?_⟩
            exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
          calls := fun h => by cases h
          slot := fun k hk => by simp [List.isEmpty_iff.1 hsl] at hk
          extra := by show 0 ≤ (8 : Int); decide
          frame := ⟨by show 4096 + 8 ≤ GenG2.sp0.toNat; decide,
            by show GenG2.sp0.toNat + 8 ≤ 2 ^ 64; decide, fun k off h => by cases h⟩ }
        vars := by
          intro x hx
          simp [List.isEmpty_iff.1 hav] at hx }
      wbs := fun h => by cases h }
    icalls := fun h => by cases h }
  memeqs := fun h => by cases h

/-! ## `v8`: `LDAR (R0), R0` -/

theorem sep0 : SepFrom GenG14.ι (StkAt E) GenG14.mem7 := by
  intro b al a h ha y hy
  obtain ⟨rfl, rfl⟩ := GenG14.mem7_blocks h
  have ha' : a = GenG14.A := by simp [GenG14.ι, GenG12.ι] at ha; exact ha.symm
  subst ha'
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    have hA : GenG14.A.toNat = 0x20000000000 := rfl
    rw [hsp] at h2
    simp only [hA, Array.size_ofFn]
    omega
  · cases hk

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .ptr GenG14.pQ) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 2 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact ⟨GenG14.A, rfl, by decide⟩
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG14.mem7, rfl, GenG14.memInj7⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl,
    by simp only [MState.word, readMem, m0, GenG14.M7, E, GenG14.A]; decide,
    by simp only [MState.word, readMem, m0, GenG14.M7, E, GenG14.A]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g38Inv0 (h0 : (kAt lc kt 1 blk 2).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk 2) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG14.mem7, rfl, GenG14.keys7, sep0⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of G14 at `v8`, an `LDAR`: none apply. -/
theorem pre8 {s : LocState} (hop : (val 8).op = .ARM64LDAR) : G14Pre lc s (val 8) := by
  have hne : ∀ o : Op, o ≠ .ARM64LDAR → (val 8).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- `v8` reads 8 valid bytes of `heap 1` at `GenG14.pQ`. -/
theorem ldarPre8 (hop : (val 8).op = .ARM64LDAR) (ha0 : (val 8).args[0]? = some 6)
    (hq : addrIsQ s0 = true) (hrd : (GenG14.mem7.read GenG14.pQ 8).isSome = true) :
    LdarPre lc s0 (val 8) := by
  intro as n hl a x h0 hx
  rw [hop] at hl
  simp only [ldar?, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨-, rfl⟩ := hl
  rw [ha0] at h0
  cases h0
  obtain ⟨x', hx', hp⟩ := addrIsQ_spec hq
  rw [hx] at hx'
  cases hx'
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hrd
  exact ⟨GenG14.pQ, GenG14.mem7, bs, hp, rfl, hbs⟩

/-- **G38 on `sync/atomic.LoadInt64`**: from the state with `addr` the pointer to the word 7 of
`heap 1` in `R0`, `g38_value` runs `v8 = LDAR v6 v1` (`LDAR (R0), R0`): `runLoc`'s `R0` holds 7,
and the machine state, related to it before `v10` under an activation extending `E` that is again
a `G28Env`, has `X0 = 7`. `checkG37` rejects the function. -/
theorem genG38_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 8) = .ok s1 ∧ s1.regs[0]? = some (.i64 7) ∧
      (checkG37 lc ps bs g).toOption = none ∧
      E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E1 s1 1 3 m1 ∧ m1.x 0 = 7 := by
  obtain ⟨hl, hc, h37, hav, hsl, hm1, hb, hv8, hi2, hop, ha0, hk0, hu2, hq, hrd, hrun, h7⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr0 := GenG14.r0Is7_spec hr
  have hE := g38Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64LDAR → (val 8).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g38_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm1 hb hi2 hv8 (by rw [hop]; rfl) locMatch0 (g38Inv0 hk0)
    (by rw [hu2]; intro e he; cases he) ⟨pre8 hop, ldarPre8 hop ha0 hq hrd⟩
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  refine ⟨s1, E1, m1, hs1, hr0, h37, hx1, hE1, hp1, hm1', ?_⟩
  have hrel := (hm1'.regs 0 _ hr0).1 0 (by simp [objX?])
  rcases hrel with h | ⟨hn, -⟩
  · exact h
  · exact absurd h7 hn

end GoFV.Proof.Witness.GenG38
