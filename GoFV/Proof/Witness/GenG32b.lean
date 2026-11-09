import GoFV.Proof.Gen.G32
import GoFV.Proof.Witness.GenG13

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G32 of the genssa validator on `(*atomicOffAddr).StoreMarked`

`std/std/runtime/(*atomicOffAddr).StoreMarked,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain` (file names `%28%2AatomicOffAddr%29.StoreMarked,1.*`),
embedded verbatim (`fSsa`, `fProg`):

```go
func (b *atomicOffAddr) StoreMarked(addr uintptr) {
	b.a.Store(-int64(addr - arenaBaseOffset))
}
```

(`runtime/mranges.go`, `arenaBaseOffset = 0` on arm64, `atomic.Int64.Store` inlined).

`checkG30` rejects it (`v13: op NEG`); `checkG32` accepts it with the PC table `tab` and the class
table `kt`. Block `b2`: `v6 = ArgIntReg` (`b`, `R0`), `v7 = ArgIntReg` (`addr`, `R1`),
`v1 = InitMem`, `v13 = NEG v7` (`NEG R1, R1`), `v14 = InlMark` (`NOP`),
`v17 = STLR v6 v13 v1` (`STLR R1, (R0)`), `MakeResult`; `Ret`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g32b_facts`),
`stepLoc` runs `v13` from a state with `b` the start of the heap object `heap 1` (`GenG13.pB`) in
`R0` and `addr = xA = 0xffffffeeddccbbab` in `R1`: `R1` then holds `-xA = 0x1122334455`. It runs
`v17` (the generic `AtomicStore64`) from the state with `-xA` in `R1` and `heap 1` a block of 8
bytes 7 (`mem8`): the memory is then `memW`, `heap 1` holding the 8 little-endian bytes of `-xA`
(below `2 ^ 40`, so they encode no pointer). On a framed activation with `G28Env` with `heap 1` at
`GenG13.A` (its bytes there, `M8`), `g32_value` runs the `NEG`: the machine's `X1` is `-xA`
(`genG32_un_witness`); and it runs the `STLR`: the machine's 8 bytes at `GenG13.A` read as `-xA`
(`genG32_stlr_witness`).
-/

namespace GoFV.Proof.Witness.GenG32b

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/(*atomicOffAddr).StoreMarked,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "(*atomicOffAddr).StoreMarked" 1 0 0
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
type t5 STRUCT 0 1 0 comparable,named "atomic.noCopy" "internal/runtime/atomic.noCopy" 0
type t6 STRUCT 0 8 0 comparable,named "atomic.align64" "internal/runtime/atomic.align64" 0
type t7 INT64 8 8 0 comparable,named "int64" "int64"
type t4 STRUCT 8 8 0 comparable,named "atomic.Int64" "internal/runtime/atomic.Int64" 3
field 0 "noCopy" t5 0 0
field 1 "_" t6 0 0
field 2 "value" t7 0 0
type t3 STRUCT 8 8 0 comparable,named "atomicOffAddr" "runtime.atomicOffAddr" 1
field 0 "a" t4 0 0
type t2 PTR 8 8 8 hasptr,direct,comparable "*atomicOffAddr" "*runtime.atomicOffAddr" t3
type t8 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t1 FUNC 8 8 8 hasptr,direct "method(*atomicOffAddr) func(uintptr)" "method(*runtime.atomicOffAddr) func(uintptr)" 1 1 0
field 0 "b" t2 ? 0
field 1 "addr" t8 ? 0
aux a2 sym "runtime.(*atomicOffAddr).StoreMarked" "runtime.(*atomicOffAddr).StoreMarked" 1 - 0 - - - - 0
posbase p32 "runtime/mranges.go" 1 1 -1
aux a3 name "b" "b" PPARAM t2 0 1 used p32:216:7:0:0
aux a4 name "addr" "addr" PPARAM t8 8 1 used p32:216:37:0:0
aux a1 call "AuxCall{runtime.(*atomicOffAddr).StoreMarked}" a2 1 2 0 8 16 2 0
abiparam in 0 t2 a3 0 0
abiparam in 1 t8 a4 1 8
type t9 BOOL 1 1 0 comparable,named "bool" "bool"
type t10 INT8 1 1 0 comparable,named "int8" "int8"
type t11 INT16 2 2 0 comparable,named "int16" "int16"
type t12 INT32 4 4 0 comparable,named "int32" "int32"
type t13 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t14 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t15 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t16 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t17 INT 8 8 0 comparable,named "int" "int"
type t18 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t19 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t20 UINT 8 8 0 comparable,named "uint" "uint"
type t21 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t22 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t13
type t23 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t12
type t24 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t15
type t25 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t17
type t26 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t8
type t27 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t18
type t28 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t19
type t29 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t22
type t30 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t31 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t32 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t33 SSA ? ? ? - "mem" ""
type t34 SSA ? ? ? - "flags" ""
type t35 SSA ? ? ? - "void" ""
type t36 SSA 16 8 ? - "int128" ""
type t37 RESULTS ? ? ? - "mem" "" 1 t33
type t38 PTR 8 8 8 hasptr,direct,comparable "**atomicOffAddr" "**runtime.atomicOffAddr" t2
type t39 PTR 8 8 8 hasptr,direct,comparable "*atomic.Int64" "*internal/runtime/atomic.Int64" t4
posbase p580 "internal/runtime/atomic/types.go" 1 1 307
type t40 PTR 8 8 8 hasptr,direct,comparable "*int64" "*int64" t7
slot s1 a3 t2 0 - 0
slot s2 a4 t8 0 - 0
aux a5 name "atomic.i" "i" PAUTO t39 0 1 used p580:80:7:0:0
slot s3 a5 t39 0 - 0
aux a6 name "atomic.value" "value" PAUTO t7 0 1 used p580:80:23:0:0
slot s4 a6 t7 0 - 0
f b1 t1 a1 19 2
typs Bool=t9,Int8=t10,Int16=t11,Int32=t12,Int64=t7,UInt8=t13,UInt16=t14,UInt32=t15,UInt64=t16,Int=t17,Float32=t18,Float64=t19,UInt=t20,Uintptr=t8,String=t21,BytePtr=t22,Int32Ptr=t23,UInt32Ptr=t24,IntPtr=t25,UintptrPtr=t26,Float32Ptr=t27,Float64Ptr=t28,BytePtrPtr=t29,Complex64=t30,Complex128=t31,UnsafePtr=t32,Mem=t33,Flags=t34,Void=t35,Int128=t36,ResultMem=t37
b b1 Plain p32:217:11:0:0 0 0 - - b2:0 -
v v1 InitMem t33 0 - p0:0:0:0:0 6 -
v v2 SP t8 0 - p0:0:0:0:0 2 -
v v3 SB t8 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t38 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t26 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:0:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v10 Const64 t8 0 - p0:0:0:0:0 1 -
v v11 Sub64 t8 0 - p32:217:24:0:0 1 v7,v10
v v12 Copy t7 0 - p32:217:24:2:0 1 v11
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v12
v v14 InlMark t35 307 - p32:217:11:1:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:0:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 1 v16,v13,v1
b b2 Ret p32:218:1:0:0 0 0 - v19 - b1:0
v v18 Copy t33 0 - p32:218:1:2:0 1 v17
v v19 MakeResult t37 0 - p32:218:1:0:0 1 v18
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts 0=v10
freev -
freeb -
dcllen 5
end
pass 1 "number lines"
f b1 t1 a1 19 2
b b1 Plain p32:217:11:1:0 0 0 - - b2:0 -
v v1 InitMem t33 0 - p0:0:0:0:0 6 -
v v2 SP t8 0 - p0:0:0:0:0 2 -
v v3 SB t8 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t38 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t26 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v10 Const64 t8 0 - p0:0:0:0:0 1 -
v v11 Sub64 t8 0 - p32:217:24:0:0 1 v7,v10
v v12 Copy t7 0 - p32:217:24:2:0 1 v11
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v12
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:1:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 1 v16,v13,v1
b b2 Ret p32:218:1:0:0 0 0 - v19 - b1:0
v v18 Copy t33 0 - p32:218:1:2:0 1 v17
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v18
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts 0=v10
freev -
freeb -
cache postorder b2,b1
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 19 2
b b1 Plain p32:217:11:1:0 0 0 - - b2:0 -
v v1 InitMem t33 0 - p0:0:0:0:0 6 -
v v2 SP t8 0 - p0:0:0:0:0 2 -
v v3 SB t8 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t38 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t26 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v10 Const64 t8 0 - p0:0:0:0:0 1 -
v v11 Sub64 t8 0 - p32:217:24:0:0 2 v7,v10
v v12 Copy t7 0 - p32:217:24:2:0 0 v11
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v11
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:1:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 2 v16,v13,v1
b b2 Ret p32:218:1:0:0 0 0 - v19 - b1:0
v v18 Copy t33 0 - p32:218:1:2:0 0 v17
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts 0=v10
freev -
freeb -
cache postorder b2,b1
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 3 "early deadcode"
f b1 t1 a1 19 2
b b1 Plain p32:217:11:1:0 0 0 - - b2:0 -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v10 Const64 t8 0 - p0:0:0:0:0 1 -
v v11 Sub64 t8 0 - p32:217:24:0:0 1 v7,v10
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v11
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:1:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 1 v16,v13,v1
b b2 Ret p32:218:1:0:0 0 0 - v19 - b1:0
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts 0=v10
freev v18,v12,v5,v4,v3,v2
freeb -
cache postorder b2,b1
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 4 "short circuit"
f b2 t1 a1 19 2
b b1 BlockInvalid p32:217:11:1:0 0 0 - - - -
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v10 Const64 t8 0 - p0:0:0:0:0 1 -
v v11 Sub64 t8 0 - p32:217:24:0:0 1 v7,v10
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v11
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:1:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts 0=v10
freev v18,v12,v5,v4,v3,v2
freeb -
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 5 "decompose user"
f b2 t1 a1 19 2
b b1 BlockInvalid p32:217:11:1:0 0 0 - - - -
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v10 Const64 t8 0 - p0:0:0:0:0 1 -
v v11 Sub64 t8 0 - p32:217:24:0:0 1 v7,v10
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v11
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:1:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts 0=v10
freev v18,v12,v5,v4,v3,v2
freeb -
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 6 "pre-opt deadcode"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v10 Const64 t8 0 - p0:0:0:0:0 1 -
v v11 Sub64 t8 0 - p32:217:24:0:0 1 v7,v10
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v11
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:1:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts 0=v10
freev v18,v12,v5,v4,v3,v2
freeb b1
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 7 "opt"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:1:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 8 "zero arg cse"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:1:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 9 "opt deadcode"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:1:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 10 "generic cse"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:1:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 11 "phiopt"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:1:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 12 "gcse deadcode"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v15 NilCheck t39 0 - p580:81:15:1:0 1 v9,v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:0:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 13 "nilcheckelim"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v15 Copy t39 0 - p580:81:15:1:0 1 v9
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 14 "prove"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v15 Copy t39 0 - p580:81:15:1:0 1 v9
v v16 OffPtr t40 0 - p580:81:15:0:0 1 v15
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 15 "divisible"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v16 OffPtr t40 0 - p580:81:15:1:0 1 v9
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v15,v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 16 "divmod"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v9 OffPtr t39 0 - p32:217:3:0:0 1 v8
v v16 OffPtr t40 0 - p580:81:15:1:0 1 v9
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v15,v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 17 "middle opt"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v9,v15,v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 18 "known bits"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v9,v15,v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 19 "early fuse"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p32:216:6:2:0 1 -
v v7 Arg t8 0 a4 p32:216:6:2:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v9,v15,v18,v11,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 20 "expand calls"
aux a7 nameoff "b+0" a3 0
aux a8 nameoff "addr+0" a4 0
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
v v9 SB t8 0 - p0:0:0:0:0 0 -
v v15 SP t8 0 - p0:0:0:0:0 2 -
v v18 OffPtr t38 0 - p0:0:0:0:0 0 v15
v v11 OffPtr t26 0 - p0:0:0:0:0 0 v15
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts 0=v18,v11
freev v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 21 "decompose builtin"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
v v9 SB t8 0 - p0:0:0:0:0 0 -
v v15 SP t8 0 - p0:0:0:0:0 2 -
v v18 OffPtr t38 0 - p0:0:0:0:0 0 v15
v v11 OffPtr t26 0 - p0:0:0:0:0 0 v15
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts 0=v18,v11
freev v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 22 "softfloat"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
v v9 SB t8 0 - p0:0:0:0:0 0 -
v v15 SP t8 0 - p0:0:0:0:0 2 -
v v18 OffPtr t38 0 - p0:0:0:0:0 0 v15
v v11 OffPtr t26 0 - p0:0:0:0:0 0 v15
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts 0=v18,v11
freev v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 23 "branchelim"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
v v9 SB t8 0 - p0:0:0:0:0 0 -
v v15 SP t8 0 - p0:0:0:0:0 2 -
v v18 OffPtr t38 0 - p0:0:0:0:0 0 v15
v v11 OffPtr t26 0 - p0:0:0:0:0 0 v15
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts 0=v18,v11
freev v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 24 "late opt"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 25 "dead auto elim"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 26 "sccp"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s3,s4
named s1 v6
named s2 v7
named s3 v9
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 27 "generic deadcode"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 28 "late fuse"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 29 "check bce"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 30 "dse"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 31 "memcombine"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 32 "writebarrier"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 NilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 Neg64 t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v16 OffPtr t40 0 - p580:81:15:2:0 1 v8
v v17 AtomicStore64 t33 0 - p580:81:12:1:0 1 v16,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 33 "lower"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 34 "addressing modes"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 35 "late lower"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 36 "pair"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 37 "lowered deadcode for cse"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 38 "lowered cse"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 39 "elim unread autos"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 40 "tighten tuple selectors"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 41 "lowered deadcode"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 42 "checkLower"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 43 "loop invariant"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 44 "late phielim and copyelim"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 45 "tighten"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 46 "late deadcode"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 47 "critical"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 48 "phi tighten"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 49 "likelyadjust"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
dcllen 5
end
pass 50 "layout"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p32:217:3:1:0 1 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v8,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
fstate laidout
dcllen 5
end
pass 51 "schedule"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 2 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v8 ARM64LoweredNilCheck t35 0 - p32:217:3:1:0 0 v6,v1
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p580:81:12:1:0 1 v6,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81
fstate scheduled,laidout
dcllen 5
end
pass 52 "late nilcheck"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p32:217:3:1:0 1 v6,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81:81=0
fstate scheduled,laidout
dcllen 5
end
pass 53 "flagalloc"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p32:217:3:1:0 1 v6,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v16,v11,v18,v15,v9,v10,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81:81=0
fstate scheduled,laidout
dcllen 5
end
pass 54 "regalloc"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p32:217:3:1:0 1 v6,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v2,v3,v4,v5,v9,v10,v11,v12,v15,v16,v18
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81:81=0
fstate scheduled,laidout
regalloc 14 v6:R0,v7:R1,v13:R1
dcllen 5
end
pass 55 "loop rotate"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p32:217:3:1:0 1 v6,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v2,v3,v4,v5,v9,v10,v11,v12,v15,v16,v18
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81:81=0
fstate scheduled,laidout
regalloc 14 v6:R0,v7:R1,v13:R1
dcllen 5
end
pass 56 "trim"
f b2 t1 a1 19 2
b b2 Ret p32:218:1:0:0 0 0 - v19 - -
v v6 ArgIntReg t2 0 a7 p32:218:1:0:0 1 -
v v7 ArgIntReg t8 1 a8 p32:218:1:0:0 1 -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v13 ARM64NEG t7 0 - p32:217:12:0:0 1 v7
v v14 InlMark t35 307 - p32:217:11:0:0 0 v1
v v17 ARM64STLR t33 0 - p32:217:3:1:0 1 v6,v13,v1
v v19 MakeResult t37 0 - p32:218:1:1:0 1 v17
names s1,s2,s4
named s1 v6
named s2 v7
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a4/t8/0/-/0=s2,a5/t39/0/-/0=s3,a6/t7/0/-/0=s4
consts -
freev v2,v3,v4,v5,v9,v10,v11,v12,v15,v16,v18
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a7:4,a8:5
cache linestarts 32:217:218,580:81:81:81=0
fstate scheduled,laidout
regalloc 14 v6:R0,v7:R1,v13:R1
dcllen 5
end
frontend
end
ptrcache t3,t4,t5,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t26,t29,t30,t31,t32
typelink t33=t37
typeorder t10,t13,t11,t14,t12,t15,t7,t16,t17,t20,t8,t30,t31,t18,t19,t9,t22,t23,t24,t40,t25,t26,t27,t28,t29,t38,t39,t2,t1,t4,t5,t6,t3,t21,t32,t33,t35,t34,t36,t37
eof
"#

/-- `std/std/runtime/(*atomicOffAddr).StoreMarked,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "(*atomicOffAddr).StoreMarked" 1
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
type t1 8 8 8 1 01 "*atomicOffAddr"
name n1 "b" PPARAM t1 1 "runtime.b" 0 a3
type t2 8 8 0 0 - "uintptr"
name n2 "addr" PPARAM t2 1 "runtime.addr" 0 a4
type t3 8 8 8 1 01 "*atomic.Int64"
name n3 "i" PAUTO t3 1 "internal/runtime/atomic.i" 0 a5
type t4 8 8 0 0 - "int64"
name n4 "value" PAUTO t4 1 "internal/runtime/atomic.value" 0 a6
type t5 8 8 8 1 01 "*int64"
name n5 ".autotmp_4" PAUTO t5 3 "runtime..autotmp_4" 0 -
in n1 0 used
in n2 8 used
in n3 0 used
in n4 0 used
in n5 0 used,autotmp
out n1 0 used
out n2 8 used
opt n5 0 autotmp
opt n3 0 -
opt n4 0 -
stack 0 0 8
end
genin
posbase p32 "runtime/mranges.go" 1 1 -1 31 "runtime/mranges.go" "runtime/mranges.go" 1 1
sym y1 "runtime.(*atomicOffAddr).StoreMarked" 1
curfn p32:216:6:0:0 0 0
regargs 8192:0:t1,8193:8:t2
text y1 0 0 0 0 216 201080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.(*atomicOffAddr).StoreMarked.arginfo1" 0
sym y5 "runtime.(*atomicOffAddr).StoreMarked.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 0 p32:216:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p32:216:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p32:216:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p32:216:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p32:216:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p32:216:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p32:217:3:1:0
p 7 7 0 0 0 - NEG 0 REG/8193/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p32:217:3:1:0
p 8 8 0 0 0 - NOP 0 _ 0 - _ 0 0 p0:0:0:0:0
p 9 9 0 0 0 - STLR 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 0 0 p32:217:3:2:0
p 10 10 0 0 0 - RET 0 _ 0 - _ 0 0 p32:218:1:0:0
p 11 11 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 216 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
inlmark @7 307
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 2
dbgslot 0 n1 t1 0
dbgslot 1 n2 t2 0
dbgslot 2 n4 t4 0
dbgvar 0 n1 0
dbgvar 1 n2 1
dbgvar 2 n4 2
dbgloc 0 2:-10000:-1:-30000:50
dbgloc 1 2:-10000:2:13:51
dbgloc 2 2:13:-1:-30000:51
dbgregout -
dbgpc 2:13:8
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 2 p32:216:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p32:216:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p32:216:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p32:216:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p32:216:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p32:216:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p32:217:3:1:0
p 7 0 0 0 408 - NEG 0 REG/8193/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p32:217:3:1:0
p 8 4 0 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p0:0:0:0:0
p 9 4 0 0 424 - STLR 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 0 0 p32:217:3:2:0
p 10 8 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p32:218:1:0:0
fn y1 16 0 0 0 216 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
inlmark @7 307
funcaux y2 y3 - - y4 y5 -
text 16 0 e10301cb01fc9fc8c0035fd600000000 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y3,_,_,_,y4,y5
usedfiles 31
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 5 1 8000 00080808ff 0
data y5 SDATA 2 1 8000 0000 0
data y6 SRODATA 3 1 28000 010400 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 040400 0
data y10 SRODATA 3 1 28000 020400 0
data y11 SRODATA 3 1 28000 400400 0
data y12 SRODATA 6 1 28000 b40302020200 0
data y13 SRODATA 3 1 28000 000400 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.runtime.(*atomicOffAddr).StoreMarked$abstract" 0
sym y18 "" 0
sym y19 "internal/runtime/atomic.(*Int64).Store" 1
inl i307 - p32:217:11:0:0 y19 "(*Int64).Store"
posbase p580 "internal/runtime/atomic/types.go" 1 1 307 4 "internal/runtime/atomic/types.go" "internal/runtime/atomic/types.go" 1 1
posbase p5 "internal/runtime/atomic/types.go" 1 1 -1 4 "internal/runtime/atomic/types.go" "internal/runtime/atomic/types.go" 1 1
sym y20 "go:info.internal/runtime/atomic.(*Int64).Store$abstract" 0
sym y21 "go:info.*runtime.atomicOffAddr" 0
sym y22 "go:info.uintptr" 0
sym y23 "go:info.int64" 0
dwfn y14 y15 y16 y17 y18 "runtime.(*atomicOffAddr).StoreMarked" 31:216 1 0 1 4262
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y17 n1,n2
dwinlfn y19 y20
dwinldcl y19 "i" 0 p5:80:7:0:0
dwinldcl y19 "value" 0 p5:80:23:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime.atomicOffAddr" 0 0 1 p32:216:7:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "uintptr" 0 0 1 p32:216:37:0:0
dwname n5 1 0 1 0 0 0 0 0 - - "*int64" 0 0 1 p580:81:12:0:0
dwname n3 1 0 0 1 0 0 0 0 - - "*internal/runtime/atomic.Int64" 0 0 1 p580:80:7:0:0
dwname n4 1 0 0 1 0 0 0 0 - - "int64" 0 0 1 p580:80:23:0:0
var 0 0 "b" 5 1 0 0 0 8 y21 "runtime/mranges.go" 216 7 0 0 1 0 v0
var 1 0 "addr" 5 1 0 0 0 16 y22 "runtime/mranges.go" 216 37 0 1 1 0 v1
var 2 0 "value" 5 1 0 1 0 -8 y23 "internal/runtime/atomic/types.go" 80 23 308 1 1 0 v2
scope 0 0 - 0,1,2
inlcall 0 307 31:217 y20 - 1 - 2
dieref y14 2 y17 0
dieref y14 4 y17 1
dieoff y17 0:42,1:50
data y14 SDWARFFCN 29 0 0 0600000000000010019c29000000000000000029000000000000000000 6
reloc 1 4 R_DWARFSECREF 0 y17
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y17
reloc 15 4 R_DWARFSECREF 0 y15
reloc 20 4 R_DWARFSECREF 0 y17
reloc 24 4 R_DWARFSECREF 9 y15
data y15 SDWARFLOC 18 0 0 010000040010015000010000040004015100 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y18 SDWARFLINES 26 0 0 0009020000000000000000042003d30114063706380208000101 1
reloc 3 8 R_ADDR 0 y1
data y17 SDWARFABSFCN 62 0 1 0572756e74696d652e282a61746f6d69634f666641646472292e53746f72654d61726b65640001d801012262000000000000226164647200000000000000 2
reloc 46 4 R_DWARFSECREF 0 y21
reloc 57 4 R_DWARFSECREF 0 y22
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

/-- The PC table `checkG32` gives (`b2`: one entry per value `v6`, `v7`, `v1`, `v13`, `v14`,
`v17`, `v19`, then the `RET`). -/
def tab : PcTab := [(2, [5, 5, 5, 5, 8, 8, 10, 10])]

/-- The class table `checkG32` gives. -/
def kt : KTab := (match checkG32 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk2 : Block := (lc.ctx.f.block? 2).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `GenG13.A` and the PC table of `checkG32`. -/
def E : MatchEnv :=
  { lc, ι := GenG13.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The argument `addr`: `-0x1122334455`, so that the stored word `-xA = 0x1122334455` is below
`2 ^ 40` and its bytes encode no pointer. -/
def xA : BitVec 64 := 0xffffffeeddccbbab

/-- The Phase 1 memory before `v17`: `heap 1` a writable block of 8 bytes 7 (the `atomicOffAddr`
`b` points to). -/
def mem8 : Mem := { blocks := #[(.heap 1, { data := Array.replicate 8 (.b 7) })], nextHeap := 2 }

/-- The machine memory before `v17`: the 8 bytes 7 of `heap 1` at `GenG13.A`, 0 elsewhere. -/
def M8 : Memory := fun y => if (y - GenG13.A).toNat < 8 then 7 else 0

/-- The `runLoc` state with `b` (`GenG13.pB`) in `R0`, the 64-bit integer `w` in `R1`, every other
register `poison`, the memory `mem8`. -/
def sAt (w : BitVec 64) : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem8 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 0 then .ptr GenG13.pB else if i.val = 1 then .int .w64 w else .poison,
    flags := .poison, slots := [], mem := .mem mem8 }

/-- The machine before value `i` of `b2`: `X0` the address `GenG13.A` of `b`, `X1 = w`, the
activation's `g` and `FP`, the PC of value `i`, the memory `M8`. -/
def mAt (w : BitVec 64) (i : Nat) : MState :=
  { x := fun k => if k = 0 then GenG13.A else if k = 1 then w
      else if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 2 i, mem := M8 }

/-- The register holds the 64-bit integer `-xA`. -/
def isNeg : Option Val → Bool
  | some (.int .w64 x) => decide (x = -xA)
  | _ => false

theorem isNeg_spec {o : Option Val} (h : isNeg o = true) : o = some (.int .w64 (-xA)) := by
  unfold isNeg at h
  split at h
  · rw [of_decide_eq_true h]
  · cases h

/-- The bytes of `heap 1` after `v17`: `-xA = 0x1122334455`, little-endian. -/
def dataW : Array Byte := #[.b 0x55, .b 0x44, .b 0x33, .b 0x22, .b 0x11, .b 0, .b 0, .b 0]

/-- The Phase 1 memory after `v17`: `heap 1` holds `dataW`. -/
def memW : Mem := { blocks := #[(.heap 1, { data := dataW })], nextHeap := 2 }

/-- The memory is `memW`. -/
def memIsW (s : LocState) : Bool :=
  match s.mem with
  | .mem mm => decide (mm = memW)
  | _ => false

theorem memIsW_spec {s : LocState} (h : memIsW s = true) : s.mem = .mem memW := by
  unfold memIsW at h
  split at h
  · rename_i mm hmm
    rw [hmm, of_decide_eq_true h]
  · cases h

/-- A machine memory whose 8 bytes at `GenG13.A` are those of `-xA`, little-endian. -/
def MW : Memory := fun y => ((-xA) >>> (8 * (y - GenG13.A).toNat)).setWidth 8

/-- What compiled evaluation checks on `StoreMarked`: it holds an arm64 op, `checkG32` accepts it
with `tab` and `kt` and `checkG30` does not; it accesses no frame variable and has no home slot;
`b2` holds `v13` (`NEG v7`) at index 3 and `v17` (`STLR v6 v13 v1`) at index 5; `R0` and `R1`
have class 64 before both and the upper-bit table is empty there; `stepLoc` runs `v13` from
`sAt xA` to `R1 = -xA` and `v17` from `sAt (-xA)` to the memory `memW`; no 8 bytes of `dataW`
encode a pointer; and they are those of `MW` at `GenG13.A`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG32 lc ps bs g).toOption == some (tab, kt) && (checkG30 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 2 && (lc.ctx.f.block? 2).isSome &&
    (lc.ctx.f.value? 13).isSome && (lc.ctx.f.value? 17).isSome &&
    blk2.values[3]? == some 13 && blk2.values[5]? == some 17 &&
    (val 13).op == .ARM64NEG && (val 17).op == .ARM64STLR &&
    (kAt lc kt 2 blk2 3).get 0 == some 64 && (kAt lc kt 2 blk2 3).get 1 == some 64 &&
    (kAt lc kt 2 blk2 5).get 0 == some 64 && (kAt lc kt 2 blk2 5).get 1 == some 64 &&
    uL lc blk2 3 == [] && uL lc blk2 5 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc (sAt xA) (val 13)) (fun s1 => isNeg s1.regs[1]?) &&
    GenG1.okThen (stepLoc GenG2.env lc (sAt (-xA)) (val 17)) memIsW &&
    ((List.range 8).all fun o => ptrWordAt? dataW o == none) &&
    (List.range 8).all fun i => dataW[i]? == some (.b (MW (GenG13.A + BitVec.ofNat 64 i)))

theorem g32b_facts : gFacts = true := by
  native_decide

/-- The facts of `g32b_facts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG32 lc ps bs g = .ok (tab, kt) ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      2 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 2 = some blk2 ∧
      lc.ctx.f.value? 13 = some (val 13) ∧ lc.ctx.f.value? 17 = some (val 17) ∧
      blk2.values[3]? = some 13 ∧ blk2.values[5]? = some 17 ∧
      (val 13).op = .ARM64NEG ∧ (val 17).op = .ARM64STLR ∧
      (kAt lc kt 2 blk2 3).get 0 = some 64 ∧ (kAt lc kt 2 blk2 3).get 1 = some 64 ∧
      (kAt lc kt 2 blk2 5).get 0 = some 64 ∧ (kAt lc kt 2 blk2 5).get 1 = some 64 ∧
      uL lc blk2 3 = [] ∧ uL lc blk2 5 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc (sAt xA) (val 13)) (fun s1 => isNeg s1.regs[1]?) = true ∧
      GenG1.okThen (stepLoc GenG2.env lc (sAt (-xA)) (val 17)) memIsW = true ∧
      (∀ o, o < 8 → ptrWordAt? dataW o = none) ∧
      ∀ i, i < 8 → dataW[i]? = some (.b (MW (GenG13.A + BitVec.ofNat 64 i))) := by
  have hf := g32b_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.all_eq_true,
    List.mem_range] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hres⟩, -⟩, hav⟩, hsl⟩, hm2⟩, hb2s⟩, hv13s⟩, hv17s⟩, hi3⟩,
    hi5⟩, hop13⟩, hop17⟩, hk30⟩, hk31⟩, hk50⟩, hk51⟩, hu3⟩, hu5⟩, hrun13⟩, hrun17⟩, hpw⟩, hbw⟩ :=
    hf
  refine ⟨hl, ?_, hav, hsl, hm2, ?_, ?_, ?_, hi3, hi5, hop13, hop17, hk30, hk31, hk50, hk51, hu3,
    hu5, hrun13, hrun17, hpw, hbw⟩
  · revert hres; cases checkG32 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb2s
    simp [blk2, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv13s
    simp [val, hv]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv17s
    simp [val, hv]

theorem g32Env (hc : checkG32 lc ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG32_spec hl hc
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG32_spec hl hc
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

theorem mem8_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ mem8.blocks) :
    b = .heap 1 ∧ al = { data := Array.replicate 8 (.b 7) } := by
  simpa [mem8] using h

/-- `mem8` injected into `M8` by `GenG13.ι`: `heap 1`'s bytes 7 at `GenG13.A`. -/
theorem memInj8 : MemInj GenG13.ι mem8 M8 where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := mem8_blocks h
    exact ⟨GenG13.A, rfl, fun _ => by decide, by simp [GenG13.A]⟩
  inj := by
    intro b al b' al' a a' h h' hne
    obtain ⟨rfl, -⟩ := mem8_blocks h
    obtain ⟨rfl, -⟩ := mem8_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    obtain ⟨rfl, rfl⟩ := mem8_blocks h
    have ha' : a = GenG13.A := by simp [GenG13.ι, GenG12.ι] at ha; exact ha.symm
    subst ha'
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    simp only [Array.size_replicate] at hi
    have hd : (GenG13.A + BitVec.ofNat 64 i - GenG13.A).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    simp [ByteRel, M8, hd, hi]

theorem keys8 : KeysNodup mem8 := by simp [KeysNodup, mem8]

theorem sep8 : SepFrom GenG13.ι (StkAt E) mem8 := by
  intro b al a h ha y hy
  obtain ⟨rfl, rfl⟩ := mem8_blocks h
  have ha' : a = GenG13.A := by simp [GenG13.ι, GenG12.ι] at ha; exact ha.symm
  subst ha'
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    have hA : GenG13.A.toNat = 0x20000000000 := rfl
    rw [hsp] at h2
    simp only [hA, Array.size_replicate]
    omega
  · cases hk

theorem sAt_regs {w : BitVec 64} {r : Nat} {x : Val} (h : (sAt w).regs[r]? = some x) :
    (r = 0 ∧ x = .ptr GenG13.pB) ∨ (r = 1 ∧ x = .int .w64 w) ∨ x = .poison := by
  simp only [sAt, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · split at h
      · rename_i h1; exact Or.inr (Or.inl ⟨h1, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatchAt (w : BitVec 64) (i : Nat) : LocMatch E (sAt w) 2 i (mAt w i) where
  regs := by
    intro r v hv
    rcases sAt_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact ⟨GenG13.A, rfl, by simp [mAt, GenG13.pB]⟩
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl rfl
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [sAt] at h
  mem := ⟨mem8, rfl, memInj8⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl,
    by simp only [MState.word, readMem, mAt, M8, E, GenG13.A]; decide,
    by simp only [MState.word, readMem, mAt, M8, E, GenG13.A]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem invAt {w : BitVec 64} {i : Nat} (h0 : (kAt lc kt 2 blk2 i).get 0 = some 64)
    (h1 : (kAt lc kt 2 blk2 i).get 1 = some 64) :
    G3Inv E lc (kAt lc kt 2 blk2 i) (sAt w) where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem8, rfl, keys8, sep8⟩
    rcases sAt_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · rw [h1] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [sAt] at h

/-- The per-value premises of `NEG` and `STLR`: none apply. -/
theorem preOf {s : LocState} {n : ID} (hop : (val n).op = .ARM64NEG ∨ (val n).op = .ARM64STLR) :
    G14Pre lc s (val n) := by
  rcases hop with hop | hop <;>
  · refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro h; rcases h with h | h <;> (rw [hop] at h; cases h)
    · intro _ _ _ hl; rw [hop] at hl; cases hl
    · intro h; rw [hop] at h; cases h
    · intro h; rw [hop] at h; cases h
    · intro h; rw [hop] at h; cases h
    · intro h; rw [hop] at h; cases h
    · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- `n` bytes at `a` agree in two memories that agree there. -/
theorem readMem_congr {mm mm' : Memory} : ∀ (n : Nat) (a : BitVec 64),
    (∀ j, j < n → mm (a + BitVec.ofNat 64 j) = mm' (a + BitVec.ofNat 64 j)) →
      readMem mm a n = readMem mm' a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 : mm a = mm' a := by simpa using h 0 (by omega)
    have ih : readMem mm (a + 1) n = readMem mm' (a + 1) n :=
      readMem_congr n (a + 1) fun j hj => by
        have hj' : a + BitVec.ofNat 64 (j + 1) = a + 1 + BitVec.ofNat 64 j := by bv_omega
        rw [← hj']
        exact h (j + 1) (by omega)
    simp only [readMem]
    rw [ih, h0]

/-- **G32 on `StoreMarked`, `NEG`**: from the state before `v13` with `b` in `R0` and
`addr = xA` in `R1` (`X1 = xA`), `g32_value` runs the `NEG R1, R1`: `runLoc`'s `R1` holds `-xA`
and the machine state, related to it before `v14` under an activation extending `E` that is again
a `G28Env`, has `X1 = -xA`. -/
theorem genG32_un_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc (sAt xA) (val 13) = .ok s1 ∧
      s1.regs[1]? = some (.int .w64 (-xA)) ∧
      E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 (mAt xA 3) m1 ∧
      LocMatch E1 s1 2 4 m1 ∧ m1.x 1 = -xA := by
  obtain ⟨hl, hc, hav, hsl, hm2, hb, hv13, -, hi3, -, hop, -, hk0, hk1, -, -, hu, -, hrun, -⟩ :=
    facts
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hr1' := isNeg_spec hr1
  have hE := g32Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64NEG → (val 13).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g32_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm2 hb hi3 hv13 (by rw [hop]; rfl) (locMatchAt xA 3) (invAt hk0 hk1)
    (by rw [hu]; intro e he; cases he) (preOf (Or.inl hop))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  exact ⟨s1, E1, m1, hs1, hr1', hx1, hE1, hp1, hm1',
    valRel_i64 hA ((hm1'.regs 1 _ hr1').1 1 rfl)⟩

/-- **G32 on `StoreMarked`, `STLR`**: from the state before `v17` with `b` (`heap 1`, at
`GenG13.A`) in `R0`, `-xA = 0x1122334455` in `R1` and `heap 1` 8 bytes 7 (`M8` on the machine),
`g32_value` runs the `STLR R1, (R0)`: `runLoc`'s memory is `memW` (`heap 1` holding the bytes of
`-xA`), and the machine state, related to it before `v19` under an activation extending `E` that
is again a `G28Env`, holds the word `-xA = 0x1122334455` in its 8 bytes at `GenG13.A`. -/
theorem genG32_stlr_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc (sAt (-xA)) (val 17) = .ok s1 ∧ s1.mem = .mem memW ∧
      E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧
      PStar GenG2.H0 L ps.toList 0 (mAt (-xA) 5) m1 ∧
      LocMatch E1 s1 2 6 m1 ∧ readMem m1.mem GenG13.A 8 = 0x1122334455 := by
  obtain ⟨hl, hc, hav, hsl, hm2, hb, -, hv17, -, hi5, -, hop, -, -, hk0, hk1, -, hu, -, hrun,
    hpw, hbw⟩ := facts
  obtain ⟨s1, hs1, hw⟩ := GenG1.okThen_spec hrun
  have hE := g32Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64STLR → (val 17).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g32_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm2 hb hi5 hv17 (by rw [hop]; rfl) (locMatchAt (-xA) 5) (invAt hk0 hk1)
    (by rw [hu]; intro e he; cases he) (preOf (Or.inr hop))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  refine ⟨s1, E1, m1, hs1, memIsW_spec hw, hx1, hE1, hp1, hm1', ?_⟩
  obtain ⟨mm, hmm, hMI⟩ := hm1'.mem
  rw [memIsW_spec hw] at hmm
  cases hmm
  obtain ⟨W, hW⟩ := hMI.bytes
  have hA : E1.ι (.heap 1) = some GenG13.A := hx1.2 _ _ rfl
  obtain ⟨hwd, -, hby⟩ := hW (.heap 1) { data := dataW } GenG13.A (by simp [memW]) hA
  have hnw : ∀ o, ¬ W (.heap 1) o := by
    intro o ho
    obtain ⟨p, hp, -⟩ := hwd o ho
    by_cases ho8 : o < 8
    · rw [hpw o ho8] at hp; cases hp
    · simp [ptrWordAt?, dataW] at hp; omega
  have hMW : readMem MW GenG13.A 8 = 0x1122334455 := by decide
  rw [← hMW]
  refine readMem_congr 8 GenG13.A fun j hj => ?_
  have hj8 : j < dataW.size := by simp [dataW]; omega
  have := hby j hj8 (fun o ho => absurd ho (hnw o))
  have hb := hbw j hj
  rw [Array.getElem?_eq_getElem hj8, Option.some.injEq] at hb
  rw [hb] at this
  exact this.symm

end GoFV.Proof.Witness.GenG32b
