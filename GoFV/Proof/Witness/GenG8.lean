import GoFV.Proof.Gen.G8
import GoFV.Proof.Witness.GenG2
import GoFV.SSA.Sem.Hooks

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G8 of the genssa validator on `sync_runtime_registerPoolCleanup`

`std/runtime/sync_runtime_registerPoolCleanup,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`wSsa`, `wProg`): the runtime half
of `sync.runtime_registerPoolCleanup` (`runtime/mgc.go`), `poolcleanup = f`, a pointer store with
a write barrier:

```go
func sync_runtime_registerPoolCleanup(f func()) {
	poolcleanup = f
}
```

`checkG7` rejects it (the write-barrier request `v13 = LoweredWB [2] v1`); `checkG8` accepts it
with the PC table `tab` and the class table `kt`: block `b2` holds `v12 = MOVDload` (the old
`poolcleanup`), `v13` (`CALL runtime.gcWriteBarrier2(SB)`), `v14 = Select0 v13` in `R25`,
`v15 = Select1 v13`, `v17 = STP (R0, R1), (R25)`. By compiled evaluation (`native_decide`, listed in
`scripts/axioms-allowlist.txt`; `g8_facts`), `stepLoc` runs `v13`, `v14`, `v15` from a state before
`v13` (every register `poison`, the empty memory). On a framed activation with `G8Env`
(`SP = 0x7fff0000`, every symbol at `2^40`, the Progs at `0x10000 + 4·ID`, `ret = 0`) and a hook
`H8` that does what `wbHook` does (the buffer at `wbA = 2^41` in `R25`, `R27` and the flags
garbage), which satisfies the contract `WbOK` (`wbOK8`), `g8_value` three times gives a machine
run of the Progs through the `CALL` and the hook to a state related before `v17`
(`genG8_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG8

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/runtime/sync_runtime_registerPoolCleanup,1.ssa` (quick-v10). -/
def wSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "sync_runtime_registerPoolCleanup" 1 0 0
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
type t2 FUNC 8 8 8 hasptr,direct "func()" "func()" 0 0 0
type t1 FUNC 8 8 8 hasptr,direct "func(func())" "func(func())" 0 1 0
field 0 "f" t2 ? 0
aux a2 sym "sync.runtime_registerPoolCleanup" "sync.runtime_registerPoolCleanup" 1 - 0 - - - - 0
posbase p26 "runtime/mgc.go" 1 1 -1
aux a3 name "f" "f" PPARAM t2 0 1 used p26:2166:39:0:0
aux a1 call "AuxCall{sync.runtime_registerPoolCleanup}" a2 1 1 0 8 8 1 0
abiparam in 0 t2 a3 0 0
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
type t27 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t28 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t29 SSA ? ? ? - "mem" ""
type t30 SSA ? ? ? - "flags" ""
type t31 SSA ? ? ? - "void" ""
type t32 SSA 16 8 ? - "int128" ""
type t33 RESULTS ? ? ? - "mem" "" 1 t29
type t34 PTR 8 8 8 hasptr,direct,comparable "*func()" "*func()" t2
aux a4 sym "runtime.poolcleanup" "runtime.poolcleanup" 0 - 0 - - - - 0
aux a5 type "func()" t2
slot s1 a3 t2 0 - 0
f b1 t1 a1 8 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t14,UInt=t15,Uintptr=t16,String=t17,BytePtr=t18,Int32Ptr=t19,UInt32Ptr=t20,IntPtr=t21,UintptrPtr=t22,Float32Ptr=t23,Float64Ptr=t24,BytePtrPtr=t25,Complex64=t26,Complex128=t27,UnsafePtr=t28,Mem=t29,Flags=t30,Void=t31,Int128=t32,ResultMem=t33
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:0:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:0:0 1 v7
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
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 26:2167:2168
dcllen 1
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 26:2167:2168
dcllen 1
end
pass 3 "early deadcode"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 26:2167:2168
dcllen 1
end
pass 4 "short circuit"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 26:2167:2168
dcllen 1
end
pass 5 "decompose user"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 26:2167:2168
dcllen 1
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 26:2167:2168
dcllen 1
end
pass 7 "opt"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 26:2167:2168
dcllen 1
end
pass 8 "zero arg cse"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 26:2167:2168
dcllen 1
end
pass 9 "opt deadcode"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 26:2167:2168
dcllen 1
end
pass 10 "generic cse"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 11 "phiopt"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 12 "gcse deadcode"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 13 "nilcheckelim"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 14 "prove"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 15 "divisible"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 16 "divmod"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 17 "middle opt"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 18 "known bits"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 19 "early fuse"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p26:2166:6:2:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 20 "expand calls"
aux a6 nameoff "f+0" a3 0
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
v v4 SP t16 0 - p0:0:0:0:0 1 -
v v2 OffPtr t34 0 - p0:0:0:0:0 0 v4
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
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 21 "decompose builtin"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
v v4 SP t16 0 - p0:0:0:0:0 1 -
v v2 OffPtr t34 0 - p0:0:0:0:0 0 v4
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
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 22 "softfloat"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
v v4 SP t16 0 - p0:0:0:0:0 1 -
v v2 OffPtr t34 0 - p0:0:0:0:0 0 v4
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
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 23 "branchelim"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
v v4 SP t16 0 - p0:0:0:0:0 1 -
v v2 OffPtr t34 0 - p0:0:0:0:0 0 v4
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
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 24 "late opt"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 25 "dead auto elim"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 26 "sccp"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 27 "generic deadcode"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 28 "late fuse"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 29 "check bce"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 30 "dse"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 31 "memcombine"
f b1 t1 a1 8 1
b b1 Ret p26:2168:1:0:0 0 0 - v8 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v1
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 32 "writebarrier"
aux a7 sym "runtime.writeBarrier" "runtime.writeBarrier" 0 - 0 - - - - 0
type t35 TUPLE ? ? ? - "*uintptr,mem" "" t22 t29
aux a8 type "uintptr" t16
f b1 t1 a1 21 3
b b1 If p26:2167:14:1:0 -1 0 - v11 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v6 Addr t34 0 a4 p0:0:0:0:0 2 v3
v v2 SP t16 0 - p0:0:0:0:0 0 -
v v4 Addr t20 0 a7 p26:2168:1:0:0 1 v3
v v9 Const32 t10 0 - p0:0:0:0:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 Load t10 0 - p26:2167:14:1:0 1 v4,v1
v v11 Neq32 t3 0 - p26:2167:14:1:0 1 v10,v9
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 Load t16 0 - p26:2167:14:1:0 1 v6,v1
v v13 WB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 2 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v16 OffPtr t22 0 - p26:2167:14:1:0 1 v14
v v17 Store t29 0 a8 p26:2167:14:1:0 1 v16,v5,v15
v v18 OffPtr t22 8 - p26:2167:14:1:0 1 v14
v v19 Store t29 0 a8 p26:2167:14:1:0 1 v18,v12,v17
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v19
v v21 Store t29 0 a5 p26:2167:14:1:0 1 v6,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9
freev -
freeb -
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 33 "lower"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 2 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64MOVDstore t29 0 - p26:2167:14:1:0 1 v14,v5,v15
v v19 ARM64MOVDstore t29 8 - p26:2167:14:1:0 1 v14,v12,v17
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v19
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 34 "addressing modes"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 2 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64MOVDstore t29 0 - p26:2167:14:1:0 1 v14,v5,v15
v v19 ARM64MOVDstore t29 8 - p26:2167:14:1:0 1 v14,v12,v17
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v19
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 35 "late lower"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 2 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64MOVDstore t29 0 - p26:2167:14:1:0 1 v14,v5,v15
v v19 ARM64MOVDstore t29 8 - p26:2167:14:1:0 1 v14,v12,v17
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v19
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 36 "pair"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
v v19 Copy t29 0 - p26:2167:14:1:0 1 v17
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v19
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache auxmap -:1,a3:2,a4:3
cache linestarts 26:2167:2168
dcllen 1
end
pass 38 "lowered cse"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
dcllen 1
end
pass 39 "elim unread autos"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
dcllen 1
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
dcllen 1
end
pass 41 "lowered deadcode"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
dcllen 1
end
pass 42 "checkLower"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
dcllen 1
end
pass 43 "loop invariant"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
dcllen 1
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
dcllen 1
end
pass 45 "tighten"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
dcllen 1
end
pass 46 "late deadcode"
f b1 t1 a1 22 3
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
dcllen 1
end
pass 47 "critical"
f b1 t1 a1 22 4
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b4:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b4:0,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
b b4 Plain p26:2167:14:1:0 0 0 - - b3:0 b1:1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
dcllen 1
end
pass 48 "phi tighten"
f b1 t1 a1 22 4
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b4:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b4:0,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
b b4 Plain p26:2167:14:1:0 0 0 - - b3:0 b1:1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
dcllen 1
end
pass 49 "likelyadjust"
f b1 t1 a1 22 4
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b4:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b4:0,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
b b4 Plain p26:2167:14:1:0 0 0 - - b3:0 b1:1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:b3:11:14,b3:b1:-:-:17:20,b4:b1:-:b2:5:8
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
dcllen 1
end
pass 50 "layout"
f b1 t1 a1 22 4
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b4:0 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b4 Plain p26:2167:14:1:0 0 0 - - b3:0 b1:1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b4:0,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
fstate laidout
dcllen 1
end
pass 51 "schedule"
f b1 t1 a1 22 4
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b4:0 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b4 Plain p26:2167:14:1:0 0 0 - - b3:0 b1:1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b4:0,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
fstate scheduled,laidout
dcllen 1
end
pass 52 "late nilcheck"
f b1 t1 a1 22 4
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b4:0 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b4 Plain p26:2167:14:1:0 0 0 - - b3:0 b1:1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b4:0,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
fstate scheduled,laidout
dcllen 1
end
pass 53 "flagalloc"
f b1 t1 a1 22 4
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b4:0 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b4 Plain p26:2167:14:1:0 0 0 - - b3:0 b1:1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b4:0,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v19,v18,v16,v22,v11,v9,v4,v2,v6
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
fstate scheduled,laidout
dcllen 1
end
pass 54 "regalloc"
f b1 t1 a1 22 4
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b4:0 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b4 Plain p26:2167:14:1:0 0 0 - - b3:0 b1:1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b4:0,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v6,v9,v11,v16,v18,v19,v22
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
fstate scheduled,laidout
regalloc 15 v3:SB,v5:R0,v10:R1,v12:R1,v13:(R25;-),v14:R25
dcllen 1
end
pass 55 "loop rotate"
f b1 t1 a1 22 4
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b4:0 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b4 Plain p26:2167:14:1:0 0 0 - - b3:0 b1:1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b4:0,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v6,v9,v11,v16,v18,v19,v22
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
fstate scheduled,laidout
regalloc 15 v3:SB,v5:R0,v10:R1,v12:R1,v13:(R25;-),v14:R25
dcllen 1
end
pass 56 "trim"
f b1 t1 a1 22 4
b b1 ARM64NZW p26:2167:14:1:0 -1 0 - v10 b2:0,b3:0 -
v v5 ArgIntReg t2 0 a6 p26:2168:1:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v10 ARM64MOVWUload t10 0 a7 p26:2167:14:1:0 1 v3,v1
b b2 Plain p26:2167:14:1:0 0 0 - - b3:1 b1:0
v v12 ARM64MOVDload t16 0 a4 p26:2167:14:1:0 1 v3,v1
v v13 ARM64LoweredWB t35 2 - p26:2167:14:1:0 2 v1
v v14 Select0 t22 0 - p26:2167:14:1:0 1 v13
v v15 Select1 t29 0 - p26:2167:14:1:0 1 v13
v v17 ARM64STP t29 0 - p26:2167:14:1:0 1 v14,v5,v12,v15
b b3 Ret p26:2168:1:0:0 0 0 - v8 - b1:1,b2:0
v v20 Phi t29 0 - p26:2167:14:2:0 1 v1,v17
v v21 ARM64MOVDstore t29 0 a4 p26:2167:14:1:0 1 v3,v5,v20
v v7 WBend t29 0 - p26:2167:14:2:0 1 v21
v v8 MakeResult t33 0 - p26:2168:1:1:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v6,v9,v11,v16,v18,v19,v22
freeb -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5
cache linestarts 26:2167:2168
fstate scheduled,laidout
regalloc 15 v3:SB,v5:R0,v10:R1,v12:R1,v13:(R25;-),v14:R25
dcllen 1
end
frontend
end
ptrcache t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t22,t25,t26,t27,t28
typelink t29=t33
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t12,t15,t16,t26,t27,t13,t14,t3,t18,t19,t20,t21,t22,t23,t24,t25,t34,t2,t1,t17,t28,t29,t31,t30,t32,t35,t33
eof
"#

/-- `std/runtime/sync_runtime_registerPoolCleanup,1.prog` (quick-v10). -/
def wProg : String := r#"gofv-prog 3
pkg "runtime"
func "sync_runtime_registerPoolCleanup" 1
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
type t1 8 8 8 1 01 "func()"
name n1 "f" PPARAM t1 1 "runtime.f" 0 a3
in n1 0 used
out n1 0 used
stack 0 0 8
end
genin
posbase p26 "runtime/mgc.go" 1 1 -1 25 "runtime/mgc.go" "runtime/mgc.go" 1 1
sym y1 "sync.runtime_registerPoolCleanup" 1
curfn p26:2166:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 2166 280080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "sync.runtime_registerPoolCleanup.arginfo1" 0
sym y5 "sync.runtime_registerPoolCleanup.argliveinfo" 0
sym y6 "runtime.writeBarrier" 0
sym y7 "runtime.poolcleanup" 0
sym y8 "runtime.gcWriteBarrier2" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p26:2166:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p26:2166:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p26:2166:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p26:2166:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p26:2166:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p26:2166:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p26:2167:14:1:0
p 7 7 0 0 0 - MOVWU 0 MEM/0/0/0/EXTERN/0/0/y6/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p26:2167:14:1:0
p 8 8 0 0 0 - CBZW 0 REG/8193/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@12 0 0 p26:2167:14:2:0
p 9 9 0 0 0 - MOVD 0 MEM/0/0/0/EXTERN/0/0/y7/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p26:2167:14:1:0
p 10 10 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y8/- 0 0 p26:2167:14:2:0
p 11 11 0 0 0 - STP 0 REGREG/8192/0/0/NONE/0/8193/-/- 0 - MEM/8217/0/0/NONE/0/0/-/- 0 0 p26:2167:14:2:0
p 12 12 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p26:2167:14:1:0
p 13 13 0 0 0 - RET 0 _ 0 - _ 0 0 p26:2168:1:0:0
p 14 14 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 2166 280080
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
dbgloc 0 1:-10000:-1:-30000:50
dbgregout -
dbgpc -
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p26:2166:6:0:0
p 15 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p26:2166:6:0:0
p 16 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p26:2166:6:0:0
p 17 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p26:2166:6:0:0
p 18 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@27 0 0 p26:2166:6:0:0
p 19 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p26:2166:6:0:0
p 20 12 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p26:2166:6:0:1
p 21 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p26:2166:6:0:0
p 22 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p26:2166:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p26:2166:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p26:2166:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p26:2166:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p26:2166:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p26:2166:6:2:0
p 6 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p26:2167:14:1:0
p 7 24 0 0 397 - MOVWU 0 MEM/0/0/0/EXTERN/110/0/y6/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p26:2167:14:1:0
p 8 32 0 0 85 - CBZW 0 REG/8193/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/12/-/@12 0 0 p26:2167:14:2:0
p 9 36 0 0 338 - MOVD 0 MEM/0/0/0/EXTERN/110/0/y7/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p26:2167:14:1:0
p 10 44 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y8/- 0 0 p26:2167:14:2:0
p 11 48 0 0 436 - STP 0 REGREG/8192/0/0/NONE/7/8193/-/- 0 - MEM/8217/0/0/NONE/77/0/-/- 0 0 p26:2167:14:2:0
p 12 52 0 0 313 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y7/- 0 0 p26:2167:14:1:0
p 13 60 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p26:2168:1:0:0
p 23 64 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p26:2168:1:0:0
p 24 68 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p26:2168:1:0:0
p 25 72 -16 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p26:2168:1:0:0
p 26 72 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p26:2166:6:0:0
p 27 72 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p26:2166:6:0:0
p 28 72 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p26:2166:6:0:0
p 29 76 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p26:2166:6:0:0
p 30 80 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y9/- 0 0 p26:2166:6:0:0
p 31 84 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p26:2166:6:0:0
p 32 84 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p26:2166:6:0:0
p 33 88 16 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@15 0 0 p26:2166:6:0:0
fn y1 8 8 0 0 2166 280080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 96 0 900b40f9ff6330eb09020054fe0f1ff8fd831ff8fd2300d11b000090610340b9a10000341b000090610340f900000094200700a91b000090600300f9fd835ff8fe0741f8c0035fd6e00700f9e3031eaa00000094e00740f9eaffff1700000000 5
reloc 24 8 R_ARM64_PCREL_LDST32 0 y6
reloc 36 8 R_ARM64_PCREL_LDST64 0 y7
reloc 44 4 R_CALLARM64 0 y8
reloc 52 8 R_ARM64_PCREL_LDST64 0 y7
reloc 80 4 R_CALLARM64 0 y9
pcln y14 y15 y16 y17 y10,y11,y12,y13 y2,y3,_,_,_,y4,y5
usedfiles 25
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y10 SRODATA 11 1 28000 000101020203010f020300 0
data y11 SRODATA 0 1 28000 - 0
data y12 SRODATA 0 1 28000 - 0
data y13 SRODATA 5 1 28000 0006041200 0
data y14 SRODATA 7 1 28000 0204200d1f0700 0
data y15 SRODATA 3 1 28000 341800 0
data y16 SRODATA 10 1 28000 ee210602090203030600 0
data y17 SRODATA 3 1 28000 001800 0
end
dwarf
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
sym y21 "" 0
sym y22 "go:info.func()" 0
dwfn y18 y19 y20 - y21 "sync.runtime_registerPoolCleanup" 25:2166 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwname n1 1 1 0 0 0 0 0 0 - - "func()" 0 0 1 p26:2166:39:0:0
var 0 0 "f" 5 1 0 0 0 8 y22 "runtime/mgc.go" 2166 39 0 0 0 0 v0
scope 0 0 - 0
data y18 SDWARFFCN 61 0 0 0373796e632e72756e74696d655f7265676973746572506f6f6c436c65616e757000000060019c1a000000f610012d660000f610000000000000000000 3
reloc 34 2 R_DWTXTADDR_U2 0 y1
reloc 52 4 R_DWARFSECREF 0 y22
reloc 56 4 R_DWARFSECREF 0 y19
data y19 SDWARFLOC 9 0 0 010000040060015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y20 SDWARFRANGE 0 0 0 - 0
data y21 SDWARFLINES 35 0 0 0009020000000000000000041a03f010140a8788065f0637065f065f60850218000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded `sync_runtime_registerPoolCleanup` (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load wSsa wProg

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

/-- The PC table `checkG8` gives (block `b2`: `v13`'s `CALL` at 10, its selections and `v17`'s
`STP` at 11). -/
def tab : PcTab := [(1, [5, 5, 5, 5, 8]), (2, [9, 10, 11, 11, 11, 12]), (3, [12, 12, 13, 13, 13])]

/-- The class map at the start of `b2`: `R0` 64 bits (the argument), `R1` 32 bits (the
`writeBarrier` flag), register 63 64 bits. -/
def k2 : KMap :=
  ((KMap.bot.setIfInBounds 0 (some 64)).setIfInBounds 1 (some 32)).setIfInBounds 63 (some 64)

/-- The class map at the start of `b3`. -/
def k3 : KMap := (KMap.bot.setIfInBounds 0 (some 64)).setIfInBounds 63 (some 64)

/-- The class table `checkG8` gives: nothing known at the entry `b1`. -/
def kt : KTab := [(1, KMap.bot), (2, k2), (3, k3)]

/-- Block `b2`: `v12 = MOVDload`, `v13 = LoweredWB [2] v1`, `v14 = Select0 v13`,
`v15 = Select1 v13`, `v17 = STP`. -/
def blk2 : Block := (lc.ctx.f.block? 2).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at their symbols and the PC table of `checkG8`. -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `runLoc` state before `v13`: every register `poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v13`: the activation's `g` and `FP`, the PC of `v13`, the memory 0. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 2 1, mem := fun _ => 0 }

/-- The write-barrier buffer's address. -/
def wbA : BitVec 64 := 0x20000000000

/-- A runtime whose every entry point is `wbHook` with the buffer at `wbA`: `R25` the buffer,
`R27` and the flags garbage, return to `X30`. -/
def H8 : Hooks := ⟨fun m => some (.ret { m with
  x := fun k => if k = 25 then wbA else if k = 27 then garbage 27 else m.x k,
  nzcv := GoFV.SSA.Sem.Flags.ofNZCV 0b0110, pc := m.x 30 })⟩

/-- `ι` with the buffer at `wbA`. -/
def ι8 : Blk → Option (BitVec 64)
  | .wbuf => some wbA
  | b => GenG2.ι b

/-- What compiled evaluation checks on `sync_runtime_registerPoolCleanup`: `checkG8` accepts it
with `tab` and `kt` and `checkG7` does not; it accesses no frame variable and has no home slot;
`b2` holds `v13`, `v14`, `v15` at 1, 2, 3; their ops, `v13`'s `[2]`; and `stepLoc` runs `v13`, `v14`,
`v15` from `s0`. -/
def gFacts : Bool :=
  (checkG8 lc ps bs g).toOption == some (tab, kt) && (checkG7 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 2 && (lc.ctx.f.block? 2).isSome &&
    (lc.ctx.f.value? 13).isSome && (lc.ctx.f.value? 14).isSome && (lc.ctx.f.value? 15).isSome &&
    blk2.values[1]? == some 13 && blk2.values[2]? == some 14 && blk2.values[3]? == some 15 &&
    (val 13).op == .ARM64LoweredWB && (val 13).auxInt.toInt == 2 &&
    (val 14).op == .Select0 && (val 15).op == .Select1 &&
    GenG1.okThen (stepLoc default lc s0 (val 13)) fun s1 =>
      GenG1.okThen (stepLoc default lc s1 (val 14)) fun s2 =>
        GenG1.okThen (stepLoc default lc s2 (val 15)) fun _ => true

theorem g8_facts : gFacts = true := by
  native_decide

/-- The facts of `g8_facts` as hypotheses. -/
theorem facts :
    checkG8 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 2 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 2 = some blk2 ∧ lc.ctx.f.value? 13 = some (val 13) ∧
      lc.ctx.f.value? 14 = some (val 14) ∧ lc.ctx.f.value? 15 = some (val 15) ∧
      blk2.values[1]? = some 13 ∧ blk2.values[2]? = some 14 ∧ blk2.values[3]? = some 15 ∧
      (val 13).op = .ARM64LoweredWB ∧ (val 13).auxInt.toInt = 2 ∧ (val 14).op = .Select0 ∧
      (val 15).op = .Select1 ∧
      (GenG1.okThen (stepLoc default lc s0 (val 13)) fun s1 =>
        GenG1.okThen (stepLoc default lc s1 (val 14)) fun s2 =>
          GenG1.okThen (stepLoc default lc s2 (val 15)) fun _ => true) = true := by
  have hf := g8_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hm2⟩, hb2s⟩, hv13⟩, hv14⟩, hv15⟩, hi1⟩, hi2⟩,
    hi3⟩, hop13⟩, haux⟩, hop14⟩, hop15⟩, hrun⟩ := hf
  have hval : ∀ n, (lc.ctx.f.value? n).isSome = true → lc.ctx.f.value? n = some (val n) := by
    intro n h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    simp [val, hv]
  refine ⟨?_, hav, hsl, hm2, ?_, hval _ hv13, hval _ hv14, hval _ hv15, hi1, hi2, hi3, hop13,
    haux, hop14, hop15, hrun⟩
  · revert hres; cases checkG8 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb2s
    simp [blk2, hb]

theorem g8Env (hc : checkG8 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G8Env lc g L ps 0 tab E where
  env := {
    env := {
      lcEq := rfl
      link := rfl
      pcOf := rfl
      retOut := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG8_spec hc
        intro p hp
        exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
      addr := GenG2.addrAgree
      glob := fun _ _ _ _ => rfl
      syms := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG8_spec hc
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
  wbs := fun h => by cases h

theorem locMatch0 : LocMatch E s0 2 1 m0 where
  regs := by
    intro r v hv
    simp only [s0, Array.getElem?_replicate] at hv
    split at hv
    · cases hv
      exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
    · cases hv
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g8Inv0 (K : KMap) : G3Inv E lc K s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, GenG2.keys0, GenG2.sep0⟩
    simp only [s0, Array.getElem?_replicate] at hv
    split at hv
    · cases hv; trivial
    · cases hv
  slots := by intro k v h; simp [s0] at h

/-- The empty memory with the buffer of `LoweredWB [2]`. -/
theorem wb2_blocks :
    (GenG2.mem0.wbAlloc 2).blocks = #[(.wbuf, { data := Array.replicate (8 * 2) .poison })] := by
  simp [Mem.wbAlloc, Mem.set, GenG2.mem0]

theorem memInj8 (mm : Memory) : MemInj ι8 (GenG2.mem0.wbAlloc 2) mm where
  nil := rfl
  mapped := by
    intro b al h
    rw [wb2_blocks] at h
    simp only [Array.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨wbA, rfl, fun _ => by decide, by decide⟩
  inj := by
    intro b al b' al' a a' h h' hne
    rw [wb2_blocks] at h h'
    simp only [Array.mem_singleton, Prod.mk.injEq] at h h'
    exact absurd (h.1.trans h'.1.symm) hne
  bytes := ⟨fun _ _ => False, by
    intro b al a h _
    rw [wb2_blocks] at h
    simp only [Array.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun o ho => ho.elim, fun o o' ho => ho.elim, fun i hi _ => ?_⟩
    simp only [Array.getElem_replicate]
    trivial⟩

/-- `wbHook`'s contract holds for `H8` at `v13` from `s0` and `m0`. -/
theorem wbOK8 (haux : (val 13).auxInt.toInt = 2) : WbOK H8 E g L lc s0 (val 13) m0 := by
  intro _ y mm m₁ _ hmm _ _ _ _ _ _ _ _ _
  have hmm' : mm = GenG2.mem0 := by
    simp only [s0, Val.mem.injEq] at hmm
    exact hmm.symm
  subst hmm'
  rw [haux, show (2 : Int).toNat = 2 from rfl]
  refine ⟨ι8, _, rfl, fun b a h => ?_, fun b n a hb ha hnt => ?_, rfl, rfl,
    fun k h25 h27 => by
      show (if k = 25 then wbA else if k = 27 then garbage 27 else m₁.x k) = m₁.x k
      split <;> (try split) <;> simp_all,
    rfl, by simp [ι8], memInj8 _,
    by simp [KeysNodup, wb2_blocks], ?_⟩
  · cases b <;> first | exact h | simp [E, GenG2.ι] at h
  · cases b <;> first | exact GenG2.addrAgree _ n a hb ha hnt | simp [Blk.base?] at hb
  · intro b al a h ha y hy
    rw [wb2_blocks] at h
    simp only [Array.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [ι8, Option.some.injEq] at ha
    subst ha
    have hsp : E.sp.toNat = 0x7fff0000 := rfl
    have hA : wbA.toNat = 0x20000000000 := rfl
    rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
    · omega
    · cases hk

theorem callOK8_ne {E' : MatchEnv} {s s' : LocState} {v : Value} {m : MState}
    (h : v.op ≠ .ARM64CALLstatic) : CallOK H8 E' g L lc s s' v m :=
  fun hop => absurd hop h

theorem wbOK8_ne {E' : MatchEnv} {s : LocState} {v : Value} {m : MState}
    (h : v.op ≠ .ARM64LoweredWB) : WbOK H8 E' g L lc s v m :=
  fun hop => absurd hop h

theorem g7Pre_of {v : Value} (h1 : v.op ≠ .ARM64CMP) (h2 : v.op ≠ .ARM64CMPconst)
    (h3 : loadOp? v.op = none) (h4 : v.op ≠ .ARM64LDP) (h5 : v.op ≠ .ARM64SUB)
    (h6 : v.op ≠ .ARM64LoweredNilCheck) (s : LocState) : G7Pre lc s v :=
  ⟨⟨⟨fun h => by rcases h with h | h <;> contradiction,
    (fun _ _ _ hl => by rw [h3] at hl; cases hl), fun h => absurd h h5⟩, fun h => absurd h h4⟩,
    fun h => absurd h h6⟩

/-- **G8 on `sync_runtime_registerPoolCleanup`**: from the state before `v13`, the write-barrier
request `v13` (`CALL runtime.gcWriteBarrier2(SB)`, the hook `H8`), its buffer pointer `v14` and its
memory `v15` are matched by a machine run of the Progs to a state related before `v17`, with the
registers at their classes, under an activation that extends `E` (by the buffer) and is a
`G8Env`. -/
theorem genG8_value_witness :
    ∃ s1 s2 s3 E' m3, stepLoc default lc s0 (val 13) = .ok s1 ∧
      stepLoc default lc s1 (val 14) = .ok s2 ∧ stepLoc default lc s2 (val 15) = .ok s3 ∧
      E.Extends E' ∧ G8Env lc g L ps 0 tab E' ∧ PStar H8 L ps.toList 0 m0 m3 ∧
      LocMatch E' s3 2 4 m3 ∧ G3Inv E' lc (kAt lc kt 2 blk2 4) s3 := by
  obtain ⟨hc, hav, hsl, hm2, hb, hv13, hv14, hv15, hi1, hi2, hi3, hop13, haux, hop14, hop15,
    hrun⟩ := facts
  obtain ⟨s1, hs1, hrun⟩ := GenG1.okThen_spec hrun
  obtain ⟨s2, hs2, hrun⟩ := GenG1.okThen_spec hrun
  obtain ⟨s3, hs3, -⟩ := GenG1.okThen_spec hrun
  have hE := g8Env hc hav hsl
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, hinv1⟩ := g8_value (H := H8) (env := default) hc hE hm2
    hb hi1 hv13 (by rw [hop13]; rfl) locMatch0 (g8Inv0 _)
    (g7Pre_of (by rw [hop13]; decide) (by rw [hop13]; decide)
      (by rw [hop13]; simp [loadOp?, narrowLoad?]) (by rw [hop13]; decide) (by rw [hop13]; decide)
      (by rw [hop13]; decide) _)
    (callOK8_ne (by rw [hop13]; decide)) (wbOK8 haux) hs1
  obtain ⟨E2, m2, hx2, hE2, hp2, hm2', hinv2⟩ := g8_value (H := H8) (env := default) hc hE1 hm2
    hb hi2 hv14 (by rw [hop14]; rfl) hm1 hinv1
    (g7Pre_of (by rw [hop14]; decide) (by rw [hop14]; decide)
      (by rw [hop14]; simp [loadOp?, narrowLoad?]) (by rw [hop14]; decide) (by rw [hop14]; decide)
      (by rw [hop14]; decide) _)
    (callOK8_ne (by rw [hop14]; decide)) (wbOK8_ne (by rw [hop14]; decide)) hs2
  obtain ⟨E3, m3, hx3, hE3, hp3, hm3, hinv3⟩ := g8_value (H := H8) (env := default) hc hE2 hm2
    hb hi3 hv15 (by rw [hop15]; rfl) hm2' hinv2
    (g7Pre_of (by rw [hop15]; decide) (by rw [hop15]; decide)
      (by rw [hop15]; simp [loadOp?, narrowLoad?]) (by rw [hop15]; decide) (by rw [hop15]; decide)
      (by rw [hop15]; decide) _)
    (callOK8_ne (by rw [hop15]; decide)) (wbOK8_ne (by rw [hop15]; decide)) hs3
  exact ⟨s1, s2, s3, E3, m3, hs1, hs2, hs3,
    MatchEnv.Extends.trans (MatchEnv.Extends.trans hx1 hx2) hx3, hE3,
    (hp1.trans hp2).trans hp3, hm3, hinv3⟩

end GoFV.Proof.Witness.GenG8
