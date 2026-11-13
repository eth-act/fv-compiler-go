import GoFV.Proof.Gen.G61
import GoFV.Proof.Witness.GenG14
import GoFV.Asm.ConstLoad

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G61 of the genssa validator on `sync/atomic.SwapInt64`

`std/std/sync/atomic/SwapInt64,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`;
`sync/atomic/doc.go`, implemented in `internal/runtime/atomic`), loaded on P0' (`p0PrimeSyms`, as
`gen-check` runs G56 to G61):

```go
func SwapInt64(addr *int64, new int64) (old int64)
```

Block `b1` (the entry) tests `v11 = MOVBUload` of `runtime.arm64HasATOMICS` (`TBNZ`): `b2` holds
`v13 = LoweredAtomicExchange64Variant v7 v8 v1` (`SWPALD R1, (R0), R2`), `b3` holds
`v17 = LoweredAtomicExchange64 v7 v8 v1` (`LDAXR (R0), R2; STLXR R1, (R0), R27; CBNZ R27`), with
`addr` (`v7`) in `R0`, `new` (`v8`) in `R1` and the result in `(R2;-)`. G60 has no atomic exchange,
so `checkG60` rejects the function; `checkG61` accepts it with the PC table `tab` and the class
table `kt`. The function needs no G48 mode (`needs48 lc = false`).

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g61_facts`),
`stepLoc` runs `v17` from a state with `addr` the pointer to offset 16 of the heap object `heap 1`
of `GenG14` (`mem7`: the word 7 there) in `R0` and `new = 9` in `R1` to `R2 = 7` and the word 9 at
that address. On a framed activation with `G49Env` (`heap 1` injected at `2^41`, the machine memory
`M7`; not G48's mode, `outSP = false`), `g61_value` at the mode `false` relates that step to the
machine's load-exclusive/store-exclusive loop (`genG61_witness`): the machine's `X2` is 7.
-/

namespace GoFV.Proof.Witness.GenG61

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/sync/atomic/SwapInt64,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "sync/atomic"
func "SwapInt64" 1 1 0
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
type t1 FUNC 8 8 8 hasptr,direct "func(*int64, int64) int64" "func(*int64, int64) int64" 0 2 1
field 0 "addr" t2 ? 0
field 1 "new" t3 ? 0
field 2 "old" t3 ? 0
aux a2 sym "sync/atomic.SwapInt64" "sync/atomic.SwapInt64" 1 - 0 - - - - 0
posbase p4 "sync/atomic/doc_64.go" 1 1 -1
aux a3 name "addr" "addr" PPARAM t2 0 1 used p4:14:16:0:0
aux a4 name "new" "new" PPARAM t3 8 1 used p4:14:29:0:0
aux a5 name "old" "old" PPARAMOUT t3 0 1 - p4:14:41:0:0
aux a1 call "AuxCall{sync/atomic.SwapInt64}" a2 1 2 1 8 16 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t3 a4 1 8
abiparam out 0 t3 a5 0 -1
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
type t35 PTR 8 8 8 hasptr,direct,comparable "*bool" "*bool" t4
aux a6 sym "runtime.arm64HasATOMICS" "runtime.arm64HasATOMICS" 0 - 0 - - - - 0
type t36 TUPLE ? ? ? - "uint64,mem" "" t11 t29
type t37 RESULTS ? ? ? - "int64,mem" "" 2 t3,t29
slot s1 a3 t2 0 - 0
slot s2 a4 t3 0 - 0
f b1 t1 a1 22 4
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t3,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t14,UInt=t15,Uintptr=t16,String=t17,BytePtr=t18,Int32Ptr=t19,UInt32Ptr=t20,IntPtr=t21,UintptrPtr=t22,Float32Ptr=t23,Float64Ptr=t24,BytePtrPtr=t25,Complex64=t26,Complex128=t27,UnsafePtr=t28,Mem=t29,Flags=t30,Void=t31,Int128=t32,ResultMem=t33
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t2 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t2 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v9 Const64 t3 0 - p0:0:0:0:0 0 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:0:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v12 Copy t29 0 - p1:1:0:2:0 1 v1
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v12
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v16 Copy t29 0 - p1:1:0:2:0 1 v1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v16
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts 0=v9
freev -
freeb -
dcllen 4
end
pass 1 "number lines"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t2 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t2 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v9 Const64 t3 0 - p0:0:0:0:0 0 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v12 Copy t29 0 - p1:1:0:2:0 1 v1
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v12
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v16 Copy t29 0 - p1:1:0:2:0 1 v1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v16
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts 0=v9
freev -
freeb -
cache postorder b4,b2,b3,b1
cache linestarts 1:1:1
dcllen 4
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 8 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t2 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t2 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v9 Const64 t3 0 - p0:0:0:0:0 0 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v12 Copy t29 0 - p1:1:0:2:0 0 v1
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v16 Copy t29 0 - p1:1:0:2:0 0 v1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts 0=v9
freev -
freeb -
cache postorder b4,b2,b3,b1
cache linestarts 1:1:1
dcllen 4
end
pass 3 "early deadcode"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache linestarts 1:1:1
dcllen 4
end
pass 4 "short circuit"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache linestarts 1:1:1
dcllen 4
end
pass 5 "decompose user"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache linestarts 1:1:1
dcllen 4
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache linestarts 1:1:1
dcllen 4
end
pass 7 "opt"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache linestarts 1:1:1
dcllen 4
end
pass 8 "zero arg cse"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache linestarts 1:1:1
dcllen 4
end
pass 9 "opt deadcode"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache linestarts 1:1:1
dcllen 4
end
pass 10 "generic cse"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 11 "phiopt"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 12 "gcse deadcode"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 13 "nilcheckelim"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 14 "prove"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 15 "divisible"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 16 "divmod"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 17 "middle opt"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 18 "known bits"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 19 "early fuse"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 Arg t3 0 a4 p1:1:0:2:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v16,v12,v9,v6,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 20 "expand calls"
aux a7 nameoff "addr+0" a3 0
aux a8 nameoff "new+0" a4 0
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
v v16 SP t16 0 - p0:0:0:0:0 3 -
v v12 OffPtr t34 0 - p0:0:0:0:0 0 v16
v v9 OffPtr t2 0 - p0:0:0:0:0 0 v16
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 2 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
v v6 LocalAddr t2 0 a5 p1:1:0:0:0 0 v16,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts 0=v12,v9
freev v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 21 "decompose builtin"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
v v16 SP t16 0 - p0:0:0:0:0 3 -
v v12 OffPtr t34 0 - p0:0:0:0:0 0 v16
v v9 OffPtr t2 0 - p0:0:0:0:0 0 v16
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 2 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
v v6 LocalAddr t2 0 a5 p1:1:0:0:0 0 v16,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts 0=v12,v9
freev v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 22 "softfloat"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
v v16 SP t16 0 - p0:0:0:0:0 3 -
v v12 OffPtr t34 0 - p0:0:0:0:0 0 v16
v v9 OffPtr t2 0 - p0:0:0:0:0 0 v16
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 2 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
v v6 LocalAddr t2 0 a5 p1:1:0:0:0 0 v16,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts 0=v12,v9
freev v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 23 "branchelim"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
v v16 SP t16 0 - p0:0:0:0:0 3 -
v v12 OffPtr t34 0 - p0:0:0:0:0 0 v16
v v9 OffPtr t2 0 - p0:0:0:0:0 0 v16
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 2 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
v v6 LocalAddr t2 0 a5 p1:1:0:0:0 0 v16,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts 0=v12,v9
freev v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 24 "late opt"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 25 "dead auto elim"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 26 "sccp"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 27 "generic deadcode"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 28 "late fuse"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 29 "check bce"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 30 "dse"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 31 "memcombine"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 32 "writebarrier"
f b1 t1 a1 22 4
b b1 If p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v10 Addr t35 0 a6 p0:0:0:0:0 1 v3
v v11 Load t4 0 - p1:1:0:1:0 1 v10,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 AtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 AtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 33 "lower"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 34 "addressing modes"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 35 "late lower"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 36 "pair"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 1:1:1
dcllen 4
end
pass 38 "lowered cse"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
dcllen 4
end
pass 39 "elim unread autos"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
dcllen 4
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
dcllen 4
end
pass 41 "lowered deadcode"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
dcllen 4
end
pass 42 "checkLower"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
dcllen 4
end
pass 43 "loop invariant"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
dcllen 4
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
dcllen 4
end
pass 45 "tighten"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
dcllen 4
end
pass 46 "late deadcode"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
dcllen 4
end
pass 47 "critical"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
dcllen 4
end
pass 48 "phi tighten"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
dcllen 4
end
pass 49 "likelyadjust"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
dcllen 4
end
pass 50 "layout"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
fstate laidout
dcllen 4
end
pass 51 "schedule"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 4
end
pass 52 "late nilcheck"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 4
end
pass 53 "flagalloc"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v20,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v6,v9,v12,v16,v5,v4,v2
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 4
end
pass 54 "regalloc"
aux a1 call "AuxCall{sync/atomic.SwapInt64}" a2 1 2 1 8 16 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t3 a4 1 8
abiparam out 0 t3 a5 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v10 Copy t11 0 - p1:1:0:2:0 1 v20
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v10,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v2,v4,v5,v6,v9,v12,v16
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 23 v3:SB,v7:R0,v8:R1,v10:R0,v11:R2,v13:(R2;-),v15:R2,v17:(R2;-),v19:R2,v20:R2,v22:[]
dcllen 4
end
pass 55 "loop rotate"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v10 Copy t11 0 - p1:1:0:2:0 1 v20
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v10,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v2,v4,v5,v6,v9,v12,v16
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 23 v3:SB,v7:R0,v8:R1,v10:R0,v11:R2,v13:(R2;-),v15:R2,v17:(R2;-),v19:R2,v20:R2,v22:[]
dcllen 4
end
pass 56 "trim"
f b1 t1 a1 22 4
b b1 ARM64TBNZ p1:1:0:0:0 1 0 - v11 b2:0,b3:0 -
v v7 ArgIntReg t2 0 a7 p1:1:0:0:0 2 -
v v8 ArgIntReg t3 1 a8 p1:1:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v11 ARM64MOVBUload t4 0 a6 p1:1:0:1:0 1 v3,v1
b b2 Plain p1:1:0:0:0 0 0 - - b4:0 b1:0
v v13 ARM64LoweredAtomicExchange64Variant t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v15 Select0 t11 0 - p1:1:0:0:0 1 v13
v v14 Select1 t29 0 - p1:1:0:0:0 1 v13
b b3 Plain p1:1:0:0:0 0 0 - - b4:1 b1:1
v v17 ARM64LoweredAtomicExchange64 t36 0 - p1:1:0:0:0 2 v7,v8,v1
v v19 Select0 t11 0 - p1:1:0:0:0 1 v17
v v18 Select1 t29 0 - p1:1:0:0:0 1 v17
b b4 Ret p1:1:0:1:0 0 0 - v22 - b2:0,b3:0
v v20 Phi t11 0 - p1:1:0:0:0 1 v15,v19
v v21 Phi t29 0 - p1:1:0:0:0 1 v14,v18
v v10 Copy t11 0 - p1:1:0:2:0 1 v20
v v22 MakeResult t37 0 - p1:1:0:0:0 1 v10,v21
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v2,v4,v5,v6,v9,v12,v16
freeb -
cache postorder b4,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b3:-:2:23,b2:b1:-:b4:11:14,b3:b1:-:b2:5:8,b4:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4,a7:5,a8:6
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 23 v3:SB,v7:R0,v8:R1,v10:R0,v11:R2,v13:(R2;-),v15:R2,v17:(R2;-),v19:R2,v20:R2,v22:[]
dcllen 4
end
frontend
end
ptrcache t3,t6,t7,t8,t10,t11,t12,t13,t14,t16,t17,t18,t25,t28
typelink t29=t33
typeorder t5,t8,t6,t9,t7,t10,t3,t11,t12,t15,t16,t26,t27,t13,t14,t4,t18,t19,t20,t2,t21,t22,t23,t24,t35,t25,t34,t1,t17,t28,t29,t31,t30,t32,t36,t33,t37
eof
"#

/-- `std/std/sync/atomic/SwapInt64,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "sync/atomic"
func "SwapInt64" 1
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
name n2 "new" PPARAM t2 1 "sync/atomic.new" 0 a4
name n3 "old" PPARAMOUT t2 1 "sync/atomic.old" 0 a5
name n4 ".autotmp_3" PAUTO t2 3 "sync/atomic..autotmp_3" 0 -
in n1 0 used
in n2 8 used
in n3 0 outregs
in n4 0 used,autotmp
out n1 0 used
out n2 8 used
opt n4 0 autotmp
opt n3 0 outregs
stack 0 0 8
end
genin
posbase p1 "<autogenerated>" 1 1 -1 0 "<autogenerated>" "<autogenerated>" 1 1
sym y1 "sync/atomic.SwapInt64" 1
curfn p1:1:0:0:0 0 0
regargs 8192:0:t1,8193:8:t2
text y1 0 0 23 0 1 210085
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "sync/atomic.SwapInt64.arginfo1" 0
sym y5 "sync/atomic.SwapInt64.argliveinfo" 0
sym y6 "runtime.arm64HasATOMICS" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 0 p1:1:0:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p1:1:0:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p1:1:0:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p1:1:0:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p1:1:0:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p1:1:0:1:0
p 7 7 0 0 0 - MOVBU 0 MEM/0/0/0/EXTERN/0/0/y6/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p1:1:0:1:0
p 8 8 0 0 0 - TBZ 0 CONST/0/0/0/NONE/0/0/-/- 8194 - BRANCH/0/0/0/NONE/0/0/-/@11 0 0 p1:1:0:2:0
p 9 9 0 0 0 - SWPALD 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 8194 0 p1:1:0:2:0
p 10 10 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@14 0 0 p1:1:0:2:0
p 11 11 0 0 0 - LDAXR 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p1:1:0:2:0
p 12 12 0 0 0 - STLXR 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 8219 0 p1:1:0:2:0
p 13 13 0 0 0 - CBNZ 0 REG/8219/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@11 0 0 p1:1:0:2:0
p 14 14 0 0 0 - MOVD 0 REG/8194/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p1:1:0:1:0
p 15 15 0 0 0 - RET 0 _ 0 - _ 0 0 p1:1:0:2:0
p 16 16 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 23 0 1 210085
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgslot 1 n2 t2 0
dbgvar 0 n1 0
dbgvar 1 n2 1
dbgloc 0 1:-10000:4:10:50
dbgloc 1 1:-10000:-1:-30000:51
dbgregout n3
dbgpc 4:10:15
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 2 p1:1:0:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p1:1:0:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p1:1:0:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p1:1:0:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p1:1:0:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p1:1:0:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:1:0
p 7 0 0 0 299 - MOVBU 0 MEM/0/0/0/EXTERN/110/0/y6/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 8 8 0 0 470 - TBZ 0 CONST/0/0/0/NONE/16/0/-/- 8194 - BRANCH/0/0/0/NONE/36/11/-/@11 0 0 p1:1:0:2:0
p 9 12 0 0 465 - SWPALD 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 8194 0 p1:1:0:2:0
p 10 16 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/14/-/@14 0 0 p1:1:0:2:0
p 11 20 0 0 234 - LDAXR 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p1:1:0:2:0
p 12 24 0 0 425 - STLXR 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 8219 0 p1:1:0:2:0
p 13 28 0 0 85 - CBNZ 0 REG/8219/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/11/-/@11 0 0 p1:1:0:2:0
p 14 32 0 0 301 - MOVD 0 REG/8194/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 15 36 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p1:1:0:2:0
fn y1 16 0 23 0 1 2100cd
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
funcaux y2 y3 - - y4 y5 -
text 48 0 1b00009062034039620000360280e1f80400001402fc5fc801fc1bc8dbffffb5e00302aac0035fd60000000000000000 1
reloc 0 8 R_ARM64_PCREL_LDST8 0 y6
pcln y11 y12 y13 y14 y7,y8,y9,y10 y2,y3,_,_,_,y4,y5
usedfiles 0
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 5 1 8000 00080808ff 0
data y5 SDATA 2 1 8000 0000 0
data y7 SRODATA 3 1 28000 010c00 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 0 1 28000 - 0
data y10 SRODATA 3 1 28000 040c00 0
data y11 SRODATA 3 1 28000 020c00 0
data y12 SRODATA 3 1 28000 020c00 0
data y13 SRODATA 3 1 28000 040c00 0
data y14 SRODATA 3 1 28000 000c00 0
end
dwarf
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
posbase p4 "sync/atomic/doc_64.go" 1 1 -1 3 "sync/atomic/doc_64.go" "sync/atomic/doc_64.go" 1 1
sym y19 "go:info.*int64" 0
sym y20 "go:info.int64" 0
sym y21 "type:int64" 0
dwfn y15 y16 y17 - y18 "sync/atomic.SwapInt64" 0:1 1 0 1 127
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2,n3
dwname n1 1 1 0 0 0 0 0 0 - - "*int64" 0 0 1 p4:14:16:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "int64" 0 0 1 p4:14:29:0:0
dwname n4 1 0 1 0 0 0 0 0 - - "int64" 0 0 1 p1:1:0:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "int64" 0 0 1 p4:14:41:0:0
var 0 0 "addr" 5 1 0 0 0 8 y19 "sync/atomic/doc_64.go" 14 16 0 0 0 0 v0
var 1 0 "new" 5 1 0 0 0 16 y20 "sync/atomic/doc_64.go" 14 29 0 1 0 0 v1
var 2 0 "old" 5 1 1 0 0 0 y20 "sync/atomic/doc_64.go" 14 41 0 2 0 0 -
scope 0 0 - 0,1,2
data y15 SDWARFFCN 78 0 0 0373796e632f61746f6d69632e53776170496e74363400000030019c0100000001012d6164647200000e00000000000000002d6e657700000e00000000000000002e6f6c6400010e000000000000 7
reloc 0 0 R_USETYPE 0 y21
reloc 23 2 R_DWTXTADDR_U2 0 y1
reloc 42 4 R_DWARFSECREF 0 y19
reloc 46 4 R_DWARFSECREF 0 y16
reloc 57 4 R_DWARFSECREF 0 y20
reloc 61 4 R_DWARFSECREF 9 y16
reloc 72 4 R_DWARFSECREF 0 y20
data y16 SDWARFLOC 18 0 0 010000040024015000010000040030015100 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
data y17 SDWARFRANGE 0 0 0 - 0
data y18 SDWARFLINES 22 0 0 0009020000000000000000065f06ff0637020c000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`) with P0' (`p0PrimeSyms`, as `gen-check`
runs G56 to G61). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) := do
  let (lc, ps, bs, g) ← GenG2.load fSsa fProg
  let (syms', ps') ← GoFV.Asm.p0PrimeSyms g.syms ps
  return (lc, ps', bs, { g with syms := syms' })

/-- `runLoc`'s context of `SwapInt64`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G61's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG61` gives. -/
def tab : PcTab := (match checkG61 lc0 ps bs g with
  | .ok (t, _) => t
  | .error _ => [])

/-- The class table `checkG61` gives. -/
def kt : KTab := (match checkG61 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

/-- `b3`, the block of `v17`. -/
def blk : Block := (lc.ctx.f.block? 3).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0''s layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `2^41` (`GenG14.ι`) and the PC table of `checkG61`; not G48's mode
(`outSP = false`). -/
def E : MatchEnv :=
  { lc, ι := GenG14.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `runLoc` state before `v17`: `addr` the pointer to offset 16 of `heap 1` (`GenG14.pQ`) in
`R0`, `new` 9 in `R1`, every other register `poison`, the memory `GenG14.mem7` (the word 7 there). -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG14.mem7 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 0 then .ptr GenG14.pQ else if i.val = 1 then .int .w64 9 else .poison,
    flags := .poison, slots := [], mem := .mem GenG14.mem7 }

/-- The machine before `v17`: `X0` the address `2^41 + 16` (`addr`), `X1 = 9` (`new`), the
activation's `g` and `FP`, the PC of `v17`, the memory `GenG14.M7`. -/
def m0 : MState :=
  { x := fun k => if k = 0 then GenG14.A + 16 else if k = 1 then 9 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 3 0, mem := GenG14.M7 }

/-- The little-endian bytes of the word 9. -/
def newB : Array Byte := #[.b 9, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0]

/-- After the exchange: `R2` (`v17`'s home) holds the old word 7 and the memory has 9 at
`GenG14.pQ`. -/
def swapped (s : LocState) : Bool :=
  (match (s.regs[2]? : Option Val) with
    | some (Val.int .w64 x) => x == 7
    | _ => false) &&
  (match s.mem with
    | .mem mm => decide (mm.read GenG14.pQ 8 = some newB)
    | _ => false)

theorem swapped_spec {s : LocState} (h : swapped s = true) :
    s.regs[2]? = some (.int .w64 7) ∧ ∃ mm, s.mem = .mem mm ∧ mm.read GenG14.pQ 8 = some newB := by
  simp only [swapped, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · split at h1
    · rename_i x hx
      simp only [beq_iff_eq] at h1
      subst h1
      exact hx
    · cases h1
  · split at h2
    · rename_i mm hmm
      exact ⟨mm, hmm, of_decide_eq_true h2⟩
    · cases h2

/-- What compiled evaluation checks on `SwapInt64`: it holds an arm64 op; on P0', `checkG61`
accepts it with `tab` and `kt` and `checkG60` does not (G60 has no atomic exchange); it accesses
no frame variable, has no home slot, is of activation 0 and needs no G48 mode; G2's symbols have
no float constant; `b3` holds `v17` (`LoweredAtomicExchange64 v7 v8 v1`) at index 0, where `R0`
and `R1` have class 64 and G35's table is empty; `stepLoc` runs `v17` from `s0` to `R2 = 7` and
the word 9 at `GenG14.pQ`, and `Ptr.ofAddr` reads 7 as no block's address. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG61 lc0 ps bs g).toOption == some (tab, kt) && (checkG60 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty && lc.ctx.act == 0 &&
    needs48 lc == false &&
    lc.ctx.f.blocks.toList.contains 3 && (lc.ctx.f.block? 3).isSome &&
    (lc.ctx.f.value? 17).isSome && blk.values[0]? == some 17 &&
    (val 17).op == .ARM64LoweredAtomicExchange64 &&
    (constRo (symNames g)).isEmpty &&
    (kAt lc kt 3 blk 0).get 0 == some 64 && (kAt lc kt 3 blk 0).get 1 == some 64 &&
    uL35 lc (uIn35 lc 3) blk 0 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 17)) swapped && (Ptr.ofAddr 7).blk == .nil

theorem g61_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG61 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG60 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧ lc.ctx.act = 0 ∧
      needs48 lc = false ∧
      3 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 3 = some blk ∧
      lc.ctx.f.value? 17 = some (val 17) ∧ blk.values[0]? = some 17 ∧
      (val 17).op = .ARM64LoweredAtomicExchange64 ∧
      (constRo (symNames g)).isEmpty = true ∧
      (kAt lc kt 3 blk 0).get 0 = some 64 ∧ (kAt lc kt 3 blk 0).get 1 = some 64 ∧
      uL35 lc (uIn35 lc 3) blk 0 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 17)) swapped = true ∧
      (Ptr.ofAddr 7).blk = .nil := by
  have hf := g61_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h60, hav, hsl, hact, h48, hm3, hbs, hvs, hi0, hop, hro, hk0, hk1, hu0, hrun,
    h7⟩ := hf
  refine ⟨hl, ?_, h60, hav, hsl, hact, h48, hm3, ?_, ?_, hi0, hop, hro, hk0, hk1, hu0, hrun, h7⟩
  · revert hres; cases checkG61 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g61Env (hc : checkG61 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
    (hav : (accessedVars lc).isEmpty = true) (hsl : (homeSlots lc).isEmpty = true) :
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
                checkG61L_spec hl (checkG61_spec hc).2
              intro p hp
              exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := GenG12.addrAgree
            glob := fun _ _ _ _ => rfl
            syms := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -, -, -⟩ :=
                checkG61L_spec hl (checkG61_spec hc).2
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
    memeqs := fun h => by cases h }
  vars := by
    intro x hx
    simp [List.isEmpty_iff.1 hav] at hx

/-! ## The memory and the state -/

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

/-- G2's symbols have no float constant: `RoPre56` holds at `s0`. -/
theorem ro0 (hro : (constRo (symNames g)).isEmpty = true) : RoPre56 g s0 := by
  intro mm _
  rw [List.isEmpty_iff.1 hro]
  intro n a h
  cases h

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .ptr GenG14.pQ) ∨ (r = 1 ∧ x = .int .w64 9) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · split at h
      · rename_i _ h1; exact Or.inr (Or.inl ⟨h1, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatch0 : LocMatch E s0 3 0 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact ⟨GenG14.A, rfl, by decide⟩
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl (by decide)
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG14.mem7, rfl, GenG14.memInj7⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl,
    by simp only [MState.word, readMem, m0, GenG14.M7, E, GenG14.A]; decide,
    by simp only [MState.word, readMem, m0, GenG14.M7, E, GenG14.A]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g61Inv0 (h0 : (kAt lc kt 3 blk 0).get 0 = some 64)
    (h1 : (kAt lc kt 3 blk 0).get 1 = some 64) : G3Inv E lc (kAt lc kt 3 blk 0) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG14.mem7, rfl, GenG14.keys7, sep0⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · rw [h1] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-! ## `v17`: `LoweredAtomicExchange64` (`LDAXR (R0), R2; STLXR R1, (R0), R27; CBNZ R27`) -/

/-- The per-value premises of G54 on `v17`, `LoweredAtomicExchange64`: none of them applies. -/
theorem pre54 (hop : (val 17).op = .ARM64LoweredAtomicExchange64) : G54Pre lc s0 (val 17) := by
  have hne : ∀ o : Op, o ≠ .ARM64LoweredAtomicExchange64 → (val 17).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
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

/-- **G61 on `sync/atomic.SwapInt64`** (`v17 = LoweredAtomicExchange64 v7 v8 v1`, the
load-exclusive/store-exclusive loop of `b3`, taken without `runtime.arm64HasATOMICS`): `checkG60`
rejects the function and `checkG61` accepts it. From the state with `addr` the pointer to the word
7 of `heap 1` in `R0` and `new = 9` in `R1`, `stepLoc` runs `v17` to the old word 7 in `R2` and the
word 9 at the address, and `g61_value` (at the mode `false`, the function needing no G48 mode)
relates it to a machine state after `LDAXR (R0), R2; STLXR R1, (R0), R27; CBNZ R27` whose `X2` is 7,
under an activation extending `E` that is again a `G49Env`. -/
theorem genG61_witness :
    (checkG60 lc0 ps bs g).toOption = none ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 17) = .ok s1 ∧
        s1.regs[2]? = some (.int .w64 7) ∧
        (∃ mm, s1.mem = .mem mm ∧ mm.read GenG14.pQ 8 = some newB) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 3 1 m1 ∧ m1.x 2 = 7 := by
  obtain ⟨hl, hc, h60, hav, hsl, -, h48, hm3, hb, hv17, hi0, hop, hro, hk0, hk1, hu0, hrun, h7⟩ :=
    facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  obtain ⟨hr2, hmem⟩ := swapped_spec hr
  have hE := g61Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64LoweredAtomicExchange64 → (val 17).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g61_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 3 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm3
  have hb0 : lc0.ctx.f.block? 3 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 17 = some (val 17) := by
    rw [← liveCtx_ctx (lc := lc0)]; exact hv17
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, -, -, -⟩ := g61_value (H := GenG2.H0) (env := GenG2.env)
    (osp := false) hc hE hl0 hm0 hb0 hi0 hv0 (by rw [hop]; rfl) locMatch0 (g61Inv0 hk0 hk1)
    (fun h => by cases h) (fun h => by cases h)
    (fun h => by
      have h' : needs48 lc = true := h
      rw [h48] at h'
      cases h')
    (by change UOKL m0 (uL35 lc (uIn35 lc 3) blk 0); rw [hu0]; intro e he; cases he)
    (pre54 hop) (ro0 hro)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => by cases h) hs1
  refine ⟨h60, s1, E1, m1, hs1, hr2, hmem, hx1, hE1, hp1, hm1, ?_⟩
  have hrel := (hm1.regs 2 _ hr2).1 2 (by simp [objX?])
  rcases hrel with h | ⟨hn, -⟩
  · exact h
  · exact absurd h7 hn

end GoFV.Proof.Witness.GenG61
