import GoFV.Proof.Gen.G64
import GoFV.Proof.Witness.GenG2
import GoFV.Asm.ConstLoad

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G64 of the genssa validator on `makearray` of `test/range`

`test/range/main/makearray,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`), loaded on P0'
(`p0PrimeSyms`, as `gen-check` runs G56 to G64):

```go
func makearray() [5]int { nmake++; return [5]int{1, 2, 3, 4, 5} }
```

A frameless leaf. Its result `~r0` (aux 3, `NAME_PARAM` 0, a forgeable frame variable) is copied
from the read-only literal `main..stmp_16` (40 bytes, the `int`s 1 to 5) by two 128-bit moves:
`b1`'s value 8, `v10 = FLDPQ {main..stmp_16} [0] v3 v11` (`FLDPQ main..stmp_16(SB), (F0, F1)`),
then `v16 = FSTPQ` (`FSTPQ (F0, F1), ~r0(FP)`). G63 has no 128-bit move (`v10: op FLDPQ`), so
`checkG63` rejects the function; `checkG64` accepts it with the PC table `tab` and the class table
`kt`. The function needs no G48 mode (`needs48 lc = false`).

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g64_facts`),
`stepLoc` runs `v10` from a state `s0` whose memory holds `main..stmp_16` (`memT`) to the blob of
its first 16 bytes (`1`, `2`) in `F0` and of the next 16 (`3`, `4`) in `F1`. `QLoadPre` holds
because both reads find 16 valid bytes of the literal (`preQ`). On a frameless activation with
`G49Env` (the globals at `symA`, every other block at its Phase 1 address, `~r0`'s block at
`SP + 8`; not G48's mode, `outSP = false`), from a machine `m0` holding the literal's bytes at
`symA`, `g64_value` at the mode `false` relates that step to the machine, which runs the
`LDP Q` (`genG64_witness`): the machine's `V0` and `V1` are `Q0` and `Q1`, the literal's first
two 16-byte halves.
-/

namespace GoFV.Proof.Witness.GenG64

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/range/main/makearray,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "makearray" 1 0 0
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
type t3 INT 8 8 0 comparable,named "int" "int"
type t2 ARRAY 40 8 0 comparable "[5]int" "[5]int" t3 5
type t1 FUNC 8 8 8 hasptr,direct "func() [5]int" "func() [5]int" 0 0 1
field 0 "" t2 ? 0
aux a2 sym "main.makearray" "main.makearray" 1 - 0 - - - - 0
posbase p2 "./range.go" 1 1 -1
aux a3 name "~r0" "~r0" PPARAMOUT t2 0 1 - p2:186:18:0:0
aux a1 call "AuxCall{main.makearray}" a2 1 0 1 48 0 0 0
abiparam out 0 t2 a3 - 8
type t4 BOOL 1 1 0 comparable,named "bool" "bool"
type t5 INT8 1 1 0 comparable,named "int8" "int8"
type t6 INT16 2 2 0 comparable,named "int16" "int16"
type t7 INT32 4 4 0 comparable,named "int32" "int32"
type t8 INT64 8 8 0 comparable,named "int64" "int64"
type t9 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t10 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t11 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t12 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t13 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t14 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t15 UINT 8 8 0 comparable,named "uint" "uint"
type t16 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t17 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t18 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t9
type t19 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t7
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t11
type t21 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t3
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
type t34 PTR 8 8 8 hasptr,direct,comparable "*[5]int" "*[5]int" t2
aux a4 type "[5]int" t2
aux a5 sym "main.nmake" "main.nmake" 0 - 0 - - - - 0
aux a6 type "int" t3
aux a7 sym "main..stmp_16" "main..stmp_16" 0 SRODATA 40 local,static,contentaddressable - - 01000000000000000200000000000000030000000000000004000000000000000500000000000000 0
type t35 RESULTS ? ? ? - "[5]int,mem" "" 2 t2,t29
f b1 t1 a1 17 1
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t8,UInt8=t9,UInt16=t10,UInt32=t11,UInt64=t12,Int=t3,Float32=t13,Float64=t14,UInt=t15,Uintptr=t16,String=t17,BytePtr=t18,Int32Ptr=t19,UInt32Ptr=t20,IntPtr=t21,UintptrPtr=t22,Float32Ptr=t23,Float64Ptr=t24,BytePtrPtr=t25,Complex64=t26,Complex128=t27,UnsafePtr=t28,Mem=t29,Flags=t30,Void=t31,Int128=t32,ResultMem=t33
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 1 v2,v1
v v5 Zero t29 40 a4 p2:186:6:0:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v7 Load t3 0 - p2:187:7:0:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v10 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v11 Store t29 0 a6 p2:187:7:0:0 2 v10,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v13 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v11
v v14 Move t29 40 a4 p2:188:2:0:0 3 v13,v12,v11
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v14
v v16 Dereference t2 0 - p2:188:2:0:0 1 v15,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev -
freeb -
dcllen 1
end
pass 1 "number lines"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 1 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v10 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v11 Store t29 0 a6 p2:187:7:0:0 2 v10,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v13 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v11
v v14 Move t29 40 a4 p2:188:2:1:0 3 v13,v12,v11
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v14
v v16 Dereference t2 0 - p2:188:2:0:0 1 v15,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:186:188
dcllen 1
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 1 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v10 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v11 Store t29 0 a6 p2:187:7:0:0 2 v10,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v13 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v11
v v14 Move t29 40 a4 p2:188:2:1:0 3 v13,v12,v11
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v14
v v16 Dereference t2 0 - p2:188:2:0:0 1 v15,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:186:188
dcllen 1
end
pass 3 "early deadcode"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 1 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v10 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v11 Store t29 0 a6 p2:187:7:0:0 2 v10,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v13 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v11
v v14 Move t29 40 a4 p2:188:2:1:0 3 v13,v12,v11
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v14
v v16 Dereference t2 0 - p2:188:2:0:0 1 v15,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:186:188
dcllen 1
end
pass 4 "short circuit"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 1 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v10 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v11 Store t29 0 a6 p2:187:7:0:0 2 v10,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v13 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v11
v v14 Move t29 40 a4 p2:188:2:1:0 3 v13,v12,v11
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v14
v v16 Dereference t2 0 - p2:188:2:0:0 1 v15,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:186:188
dcllen 1
end
pass 5 "decompose user"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 1 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v10 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v11 Store t29 0 a6 p2:187:7:0:0 2 v10,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v13 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v11
v v14 Move t29 40 a4 p2:188:2:1:0 3 v13,v12,v11
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v14
v v16 Dereference t2 0 - p2:188:2:0:0 1 v15,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:186:188
dcllen 1
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 1 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v10 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v11 Store t29 0 a6 p2:187:7:0:0 2 v10,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v13 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v11
v v14 Move t29 40 a4 p2:188:2:1:0 3 v13,v12,v11
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v14
v v16 Dereference t2 0 - p2:188:2:0:0 1 v15,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:186:188
dcllen 1
end
pass 7 "opt"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 1 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v10 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v11 Store t29 0 a6 p2:187:7:0:0 2 v10,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v13 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v11
v v14 Move t29 40 a4 p2:188:2:1:0 3 v13,v12,v11
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v14
v v16 Dereference t2 0 - p2:188:2:0:0 1 v15,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:186:188
dcllen 1
end
pass 8 "zero arg cse"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 1 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v10 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v11 Store t29 0 a6 p2:187:7:0:0 2 v10,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v13 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v11
v v14 Move t29 40 a4 p2:188:2:1:0 3 v13,v12,v11
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v14
v v16 Dereference t2 0 - p2:188:2:0:0 1 v15,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:186:188
dcllen 1
end
pass 9 "opt deadcode"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 1 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v10 Addr t21 0 a5 p0:0:0:0:0 1 v3
v v11 Store t29 0 a6 p2:187:7:0:0 2 v10,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v13 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v11
v v14 Move t29 40 a4 p2:188:2:1:0 3 v13,v12,v11
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 1 v2,v14
v v16 Dereference t2 0 - p2:188:2:0:0 1 v15,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:186:188
dcllen 1
end
pass 10 "generic cse"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 3 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v10 Addr t21 0 a5 p0:0:0:0:0 0 v3
v v11 Store t29 0 a6 p2:187:7:0:0 2 v6,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v13 LocalAddr t34 0 a3 p2:188:2:0:0 0 v2,v11
v v14 Move t29 40 a4 p2:188:2:1:0 3 v4,v12,v11
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 0 v2,v14
v v16 Dereference t2 0 - p2:188:2:0:0 1 v4,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 11 "phiopt"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 3 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v10 Addr t21 0 a5 p0:0:0:0:0 0 v3
v v11 Store t29 0 a6 p2:187:7:0:0 2 v6,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v13 LocalAddr t34 0 a3 p2:188:2:0:0 0 v2,v11
v v14 Move t29 40 a4 p2:188:2:1:0 3 v4,v12,v11
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 0 v2,v14
v v16 Dereference t2 0 - p2:188:2:0:0 1 v4,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 12 "gcse deadcode"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 3 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v14 Move t29 40 a4 p2:188:2:1:0 2 v4,v12,v11
v v16 Dereference t2 0 - p2:188:2:0:0 1 v4,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev v15,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 13 "nilcheckelim"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 3 v2,v1
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v14 Move t29 40 a4 p2:188:2:1:0 2 v4,v12,v11
v v16 Dereference t2 0 - p2:188:2:0:0 1 v4,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev v15,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 14 "prove"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 3 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 2 v4,v12,v11
v v16 Dereference t2 0 - p2:188:2:0:0 1 v4,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev v15,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 15 "divisible"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 3 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 2 v4,v12,v11
v v16 Dereference t2 0 - p2:188:2:0:0 1 v4,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev v15,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 16 "divmod"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 3 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 2 v4,v12,v11
v v16 Dereference t2 0 - p2:188:2:0:0 1 v4,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev v15,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 17 "middle opt"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 3 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 2 v4,v12,v11
v v16 Dereference t2 0 - p2:188:2:0:0 1 v4,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev v15,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 18 "known bits"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 3 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 2 v4,v12,v11
v v16 Dereference t2 0 - p2:188:2:0:0 1 v4,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev v15,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 19 "early fuse"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 3 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 2 v4,v12,v11
v v16 Dereference t2 0 - p2:188:2:0:0 1 v4,v14
v v17 MakeResult t35 0 - p2:188:2:0:0 1 v16,v14
names -
splits -
canon -
consts 1=v8
freev v15,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 20 "expand calls"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 2 v4,v12,v11
v v16 OpInvalid t2 0 - p2:188:2:0:0 0 -
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 0 v2,v14
names -
splits -
canon -
consts 1=v8
freev v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 21 "decompose builtin"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 2 v4,v12,v11
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 0 v2,v14
names -
splits -
canon -
consts 1=v8
freev v16,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 22 "softfloat"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 2 v4,v12,v11
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 0 v2,v14
names -
splits -
canon -
consts 1=v8
freev v16,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 23 "branchelim"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 2 v4,v12,v11
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 LocalAddr t34 0 a3 p2:188:2:0:0 0 v2,v14
names -
splits -
canon -
consts 1=v8
freev v16,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 24 "late opt"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 1 v4,v12,v11
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts 1=v8
freev v15,v16,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 25 "dead auto elim"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 1 v4,v12,v11
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts 1=v8
freev v15,v16,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 26 "sccp"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 1 v4,v12,v11
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts 1=v8
freev v15,v16,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 27 "generic deadcode"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 1 v4,v12,v11
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts 1=v8
freev v15,v16,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 28 "late fuse"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 1 v4,v12,v11
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts 1=v8
freev v15,v16,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 29 "check bce"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 1 v4,v12,v11
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts 1=v8
freev v15,v16,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 30 "dse"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 1 v4,v12,v11
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts 1=v8
freev v15,v16,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 31 "memcombine"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 1 v4,v12,v11
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts 1=v8
freev v15,v16,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 32 "writebarrier"
f b1 t1 a1 17 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v3 SB t16 0 - p0:0:0:0:0 2 -
v v8 Const64 t3 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Addr t21 0 a5 p0:0:0:0:0 2 v3
v v12 Addr t34 0 a7 p0:0:0:0:0 1 v3
v v5 Zero t29 40 a4 p2:186:6:1:0 2 v4,v1
v v7 Load t3 0 - p2:187:7:1:0 1 v6,v5
v v9 Add64 t3 0 - p2:187:7:0:0 1 v7,v8
v v11 Store t29 0 a6 p2:187:7:0:0 1 v6,v9,v5
v v14 Move t29 40 a4 p2:188:2:1:0 1 v4,v12,v11
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts 1=v8
freev v15,v16,v13,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 33 "lower"
type t36 SSA 16 8 ? - "vec128" ""
type t37 TUPLE ? ? ? - "vec128,vec128" "" t36 t36
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 34 "addressing modes"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 35 "late lower"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 36 "pair"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 38 "lowered cse"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 39 "elim unread autos"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 41 "lowered deadcode"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 42 "checkLower"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 43 "loop invariant"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 45 "tighten"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 46 "late deadcode"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 47 "critical"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 48 "phi tighten"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 49 "likelyadjust"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
dcllen 1
end
pass 50 "layout"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
fstate laidout
dcllen 1
end
pass 51 "schedule"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
fstate scheduled,laidout
dcllen 1
end
pass 52 "late nilcheck"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
fstate scheduled,laidout
dcllen 1
end
pass 53 "flagalloc"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDaddr t34 0 a3 p0:0:0:0:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v4,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v15 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v15,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts -
freev v12,v6,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
fstate scheduled,laidout
dcllen 1
end
pass 54 "regalloc"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v12 ARM64MOVDaddr t34 0 a3 p2:186:6:2:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v12,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v6 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v6,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts -
freev v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
fstate scheduled,laidout
regalloc 19 v2:SP,v3:SB,v6:R0,v7:R0,v9:R0,v10:(F0;F1),v12:R0,v13:F0,v18:F1
dcllen 1
end
pass 55 "loop rotate"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v12 ARM64MOVDaddr t34 0 a3 p2:186:6:2:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v12,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v6 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v6,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts -
freev v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
fstate scheduled,laidout
regalloc 19 v2:SP,v3:SB,v6:R0,v7:R0,v9:R0,v10:(F0;F1),v12:R0,v13:F0,v18:F1
dcllen 1
end
pass 56 "trim"
f b1 t1 a1 18 1
b b1 Ret p2:188:2:1:0 0 0 - v17 - -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 3 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v12 ARM64MOVDaddr t34 0 a3 p2:186:6:2:0 1 v2
v v5 ARM64LoweredZero t29 40 - p2:186:6:1:0 2 v12,v1
v v7 ARM64MOVDload t3 0 a5 p2:187:7:1:0 1 v3,v5
v v9 ARM64ADDconst t3 1 - p2:187:7:0:0 1 v7
v v11 ARM64MOVDstore t29 0 a5 p2:187:7:0:0 2 v3,v9,v5
v v10 ARM64FLDPQ t37 0 a7 p2:188:2:1:0 2 v3,v11
v v13 Select0 t36 0 - p2:188:2:1:0 1 v10
v v18 Select1 t36 0 - p2:188:2:1:0 1 v10
v v16 ARM64FSTPQ t29 0 a3 p2:188:2:1:0 1 v2,v13,v18,v11
v v6 ARM64MOVDconst t12 5 - p2:188:2:1:0 1 -
v v14 ARM64MOVDstore t29 32 a3 p2:188:2:1:0 1 v2,v6,v16
v v17 MakeResult t33 0 - p2:188:2:0:0 1 v14
names -
splits -
canon -
consts -
freev v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a5:3,a7:4
cache linestarts 2:186:188
fstate scheduled,laidout
regalloc 19 v2:SP,v3:SB,v6:R0,v7:R0,v9:R0,v10:(F0;F1),v12:R0,v13:F0,v18:F1
dcllen 1
end
frontend
end
ptrcache t3,t6,t7,t8,t9,t11,t13,t14,t16,t17,t18,t25
typelink t29=t33
typeorder t5,t9,t6,t10,t7,t11,t8,t12,t3,t15,t16,t26,t27,t13,t14,t4,t18,t19,t20,t21,t22,t23,t24,t25,t34,t1,t2,t17,t28,t29,t31,t30,t32,t36,t37,t33,t35
eof
"#

/-- `test/range/main/makearray,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "makearray" 1
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
type t1 40 8 0 0 - "[5]int"
name n1 "~r0" PPARAMOUT t1 1 "main.~r0" 0 a3
in n1 0 -
out n1 0 used
stack 0 0 8
end
genin
posbase p2 "./range.go" 1 1 -1 1 "./range.go" "./range.go" 1 1
sym y1 "main.makearray" 1
curfn p2:186:6:0:0 0 0
regargs -
text y1 0 0 0 0 186 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "main.~r0" 0
sym y4 "main.nmake" 0
sym y5 "main..stmp_16" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i40 0 0 p2:186:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:186:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:186:6:0:0
p 3 3 0 0 0 - MOVD 0 ADDR/8383/0/0/PARAM/0/0/y3/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:186:6:1:0
p 4 4 0 0 0 - STP 0 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 0 0 p2:186:6:2:0
p 5 5 0 0 0 - STP 0 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/16/-/- 0 0 p2:186:6:2:0
p 6 6 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/32/-/- 0 0 p2:186:6:2:0
p 7 7 0 0 0 - MOVD 0 MEM/0/0/0/EXTERN/0/0/y4/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:187:7:1:0
p 8 8 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/1/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:187:7:2:0
p 9 9 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:187:7:2:0
p 10 10 0 0 0 - FLDPQ 0 MEM/0/0/0/EXTERN/0/0/y5/- 0 - REGREG/8224/0/0/NONE/0/8225/-/- 0 0 p2:188:2:1:0
p 11 11 0 0 0 - FSTPQ 0 REGREG/8224/0/0/NONE/0/8225/-/- 0 - MEM/8383/0/0/PARAM/0/0/y3/- 0 0 p2:188:2:2:0
p 12 12 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/5/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:188:2:2:0
p 13 13 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/PARAM/0/32/y3/- 0 0 p2:188:2:2:0
p 14 14 0 0 0 - RET 0 _ 0 - _ 0 0 p2:188:2:2:0
p 15 15 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 186 201080
funcaux y2 y2 - - - - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y5:8
autot -
dbgentry 1
dbgregout -
dbgpc -
end
asm
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i40 0 2 p2:186:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:186:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:186:6:0:0
p 3 0 0 0 325 - MOVD 0 ADDR/0/0/0/PARAM/32/0/y3/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:186:6:1:0
p 4 4 0 0 436 - STP 0 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 0 0 p2:186:6:2:0
p 5 8 0 0 436 - STP 0 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/86/16/-/- 0 0 p2:186:6:2:0
p 6 12 0 0 308 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - MEM/8192/0/0/NONE/86/32/-/- 0 0 p2:186:6:2:0
p 16 16 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-3/-/- 0 0 p2:186:6:2:0
p 7 16 0 0 338 - MOVD 0 MEM/0/0/0/EXTERN/110/0/y4/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:187:7:1:0
p 17 24 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:187:7:1:0
p 8 24 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/1/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:187:7:2:0
p 18 28 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-4/-/- 0 0 p2:187:7:2:0
p 9 28 0 0 313 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:187:7:2:0
p 19 36 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-3/-/- 0 0 p2:187:7:2:0
p 10 36 0 0 135 - FLDPQ 0 MEM/0/0/0/EXTERN/110/0/y5/- 0 - REGREG/8224/0/0/NONE/7/8225/-/- 0 0 p2:188:2:1:0
p 20 48 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-4/-/- 0 0 p2:188:2:1:0
p 11 48 0 0 218 - FSTPQ 0 REGREG/8224/0/0/NONE/7/8225/-/- 0 - MEM/0/0/0/PARAM/48/0/y3/- 0 0 p2:188:2:2:0
p 21 56 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:188:2:2:0
p 12 56 0 0 318 - MOVD 0 CONST/0/0/0/NONE/18/5/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:188:2:2:0
p 13 60 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/32/y3/- 0 0 p2:188:2:2:0
p 14 64 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:188:2:2:0
fn y1 40 0 0 0 186 2010c8
funcaux y2 y2 - - - - -
text 80 0 e02300911f7c00a91f7c01a91f1000f91b000090600340f9000400911b000090600300f91b0000907b030091600740adfb230091600700ada00080d2e01700f9c0035fd6000000000000000000000000 3
reloc 16 8 R_ARM64_PCREL_LDST64 0 y4
reloc 28 8 R_ARM64_PCREL_LDST64 0 y4
reloc 36 8 R_ADDRARM64 0 y5
pcln y7 y8 y9 y10 y6 y2,y2
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y6 SRODATA 15 1 28000 000403020401050202030102060600 0
data y7 SRODATA 3 1 28000 021400 0
data y8 SRODATA 3 1 28000 041400 0
data y9 SRODATA 8 1 28000 f602040205020b00 0
data y10 SRODATA 3 1 28000 001400 0
end
dwarf
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "go:info.main.makearray$abstract" 0
sym y15 "" 0
sym y16 "go:info.[5]int" 0
dwfn y11 y12 y13 y14 y15 "main.makearray" 1:186 1 0 1 31
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwprecursor y1 y14 n1
dwname n1 1 1 0 0 0 0 0 0 - - "[5]int" 0 0 0 p2:186:18:0:0
var 0 0 "~r0" 5 0 1 0 0 8 y16 "./range.go" 186 18 0 0 0 0 -
scope 0 0 - 0
dieoff y14 -
data y11 SDWARFFCN 25 0 0 06000000000050019c2e7e72300001ba010000000002910800 3
reloc 1 4 R_DWARFSECREF 0 y14
reloc 5 1 R_DWTXTADDR_U1 0 y1
reloc 17 4 R_DWARFSECREF 0 y16
data y12 SDWARFLOC 0 0 0 - 0
data y13 SDWARFRANGE 0 0 0 - 0
data y15 SDWARFLINES 32 0 0 0009020000000000000000040203b4011406370688065f068806870220000101 1
reloc 3 8 R_ADDR 0 y1
data y14 SDWARFABSFCN 21 0 1 056d61696e2e6d616b6561727261790001ba010100 0
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`) with P0' (`p0PrimeSyms`, as `gen-check`
runs G56 to G64). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) := do
  let (lc, ps, bs, g) ← GenG2.load fSsa fProg
  let (syms', ps') ← GoFV.Asm.p0PrimeSyms g.syms ps
  return (lc, ps', bs, { g with syms := syms' })

/-- `runLoc`'s context of `makearray`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G64's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG64` gives. -/
def tab : PcTab := (match checkG64 lc0 ps bs g with
  | .ok (t, _) => t
  | .error _ => [])

/-- The class table `checkG64` gives. -/
def kt : KTab := (match checkG64 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

/-- `b1`, the only block, whose value 8 is `v10 = FLDPQ {main..stmp_16} [0] v3 v11`. -/
def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0''s layout: the Prog with ID `n` at `0x10000 + 4n`, no frame (a frameless leaf), every
symbol at `symA`; `NAME_PARAM` 0 is `SP + 8`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 0 0 ps.toList

/-- `ι`: the nil block at 0, the globals at `symA`, every other block at its Phase 1 address
(`Blk.base?`). -/
def ι : Blk → Option (BitVec 64)
  | .nil => some 0
  | .global _ => some GenG2.symA
  | b => b.base?.map (BitVec.ofNat 64)

/-- The activation's `SP`: `~r0`'s block (`local 0 3`, at `2^62 + 3 * 2^24`) is at `SP + 8`. -/
def spT : BitVec 64 := 0x4000000002FFFFF8

/-- A frameless activation (`SP = spT`, `g = 0x9000`, `LR = 0x40`, `FP = 0`), no home slot, the
PC table of `checkG64`; not G48's mode (`outSP = false`). -/
def E : MatchEnv :=
  { lc, ι, sp := spT, slot := fun _ => none, g := 0x9000, lr := 0x40, fp := 0, framed := false,
    pcOf := pcOfTab GenG2.text ps.toList tab }

/-- Byte `i` of `main..stmp_16` (`[5]int{1, 2, 3, 4, 5}`, little-endian). -/
def byteT (i : Nat) : BitVec 8 := if i % 8 = 0 then BitVec.ofNat 8 (i / 8 + 1) else 0

/-- The 40 bytes of `main..stmp_16`. -/
def bytesT : Array Byte := Array.ofFn (n := 40) fun i => .b (byteT i.val)

/-- The Phase 1 memory: the read-only global `main..stmp_16`. -/
def memT : Mem := { blocks := #[(.global "main..stmp_16", { data := bytesT, writable := false })] }

/-- The machine memory: the bytes of `main..stmp_16` at `symA`, 0 elsewhere. -/
def MT : Memory := fun y =>
  if (y - GenG2.symA).toNat < 40 then byteT (y - GenG2.symA).toNat else 0

/-- `main..stmp_16` at offset 0 and 16 bytes above: `v10`'s two addresses. -/
def pT : Ptr := ⟨.global "main..stmp_16", 0⟩

def pT16 : Ptr := ⟨.global "main..stmp_16", 16⟩

/-- The blobs `v10` loads: bytes 0 to 15 (`1`, `2`) and 16 to 31 (`3`, `4`) of the literal. -/
def blob0 : List Byte := (List.range 16).map fun i => .b (byteT i)

def blob1 : List Byte := (List.range 16).map fun i => .b (byteT (16 + i))

/-- The 128 bits of `blob0` and `blob1`. -/
def Q0 : BitVec 128 := 0x00000000000000020000000000000001

def Q1 : BitVec 128 := 0x00000000000000040000000000000003

/-- The `runLoc` state before `v10`: every register `poison`, no slot, the memory `memT`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := memT },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem memT }

/-- The machine before `v10`: the activation's `g` and `LR`, the PC of `v10`, the memory `MT`. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 30 then 0x40 else 0,
    sp := spT, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩, pc := E.pcOf 1 8,
    mem := MT }

/-- No write barrier and no interface or closure call (`G8Env.wbs`, `G10Env.icalls` of a
frameless activation). -/
def noWbICall (lc : LocCtx) : Bool :=
  lc.ctx.f.valueTab.all fun
    | some v => v.op != .ARM64LoweredWB && (icallLead v.op).isNone
    | none => true

theorem noWbICall_spec {lc : LocCtx} (h : noWbICall lc = true) {id : ID} {v : Value}
    (hv : lc.ctx.f.value? id = some v) : v.op ≠ .ARM64LoweredWB ∧ icallLead v.op = none := by
  have h1 : lc.ctx.f.valueTab[id]? = some (some v) := by
    have hv' : (lc.ctx.f.valueTab[id]?).join = some v := hv
    cases h : lc.ctx.f.valueTab[id]? with
    | none => rw [h] at hv'; cases hv'
    | some o => rw [h] at hv'; cases o <;> simp_all
  have h2 := (Array.all_eq_true_iff_forall_mem.1 h) _ (Array.mem_of_getElem? h1)
  simpa using h2

/-- No `LoweredMemEq` (`G28Env.memeqs` of a frameless activation). -/
def noMemEq (lc : LocCtx) : Bool :=
  lc.ctx.f.valueTab.all fun
    | some v => v.op != .ARM64LoweredMemEq
    | none => true

theorem noMemEq_spec {lc : LocCtx} (h : noMemEq lc = true) {id : ID} {v : Value}
    (hv : lc.ctx.f.value? id = some v) : v.op ≠ .ARM64LoweredMemEq := by
  have h1 : lc.ctx.f.valueTab[id]? = some (some v) := by
    have hv' : (lc.ctx.f.valueTab[id]?).join = some v := hv
    cases h : lc.ctx.f.valueTab[id]? with
    | none => rw [h] at hv'; cases hv'
    | some o => rw [h] at hv'; cases o <;> simp_all
  have h2 := (Array.all_eq_true_iff_forall_mem.1 h) _ (Array.mem_of_getElem? h1)
  simpa using h2

/-- The value is the blob `bs`. -/
def isBlob (bs : List Byte) : Option Val → Bool
  | some (.blob x) => decide (x = bs)
  | _ => false

theorem isBlob_spec {bs : List Byte} {o : Option Val} (h : isBlob bs o = true) :
    o = some (.blob bs) := by
  unfold isBlob at h
  split at h
  · rw [of_decide_eq_true h]
  · cases h

/-- What compiled evaluation checks on `makearray`: it holds an arm64 op; on P0', `checkG64`
accepts it with `tab` and `kt` and `checkG63` does not (G63 has no 128-bit move); the Progs have IDs
below `2^32`; the only accessed frame variable is `~r0` (aux 3, `NAME_PARAM` 0), at `frameOff 8`;
the activation is 0, there is no home slot and it needs no G48 mode; it has no static call, write
barrier, interface or closure call or `LoweredMemEq` (it is frameless); G2's symbols have no float
constant; `b1` holds `v10` (`FLDPQ`) at index 8, where G35's table is empty; `v10`'s symbol is
`main..stmp_16` at offset 0; `memT` reads 16 bytes at 0 and at 16; `stepLoc` runs `v10` from `s0`
to `blob0` in `F0` (Go register 31) and `blob1` in `F1` (32). -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG64 lc0 ps bs g).toOption == some (tab, kt) && (checkG63 lc0 ps bs g).toOption.isNone &&
    ps.toList.all (·.id < 2 ^ 32) &&
    accessedVars lc == [3] && varOp g 3 == some (.PARAM, 0) && lc.ctx.act == 0 &&
    (homeSlots lc).isEmpty && decide (frameOff L .PARAM 0 = 8) && needs48 lc == false &&
    GenG2.noCalls lc && noWbICall lc && noMemEq lc &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 10).isSome && blk.values[8]? == some 10 &&
    (val 10).op == .ARM64FLDPQ && (val 10).id == 10 &&
    (constRo (symNames g)).isEmpty && uL35 lc (uIn35 lc 1) blk 8 == [] &&
    ((val 10).aux.bind (symOf? lc.ctx.tabs ·)).map (·.1.toStringLossy) == some "main..stmp_16" &&
    (val 10).auxInt.toInt == 0 &&
    (memT.read pT 16).isSome && (memT.read pT16 16).isSome &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 10))
      (fun s1 => isBlob blob0 s1.regs[31]? && isBlob blob1 s1.regs[32]?)

theorem g64_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG64 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG63 lc0 ps bs g).toOption = none ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧
      accessedVars lc = [3] ∧ varOp g 3 = some (.PARAM, 0) ∧ lc.ctx.act = 0 ∧
      (homeSlots lc).isEmpty = true ∧ frameOff L .PARAM 0 = 8 ∧ needs48 lc = false ∧
      GenG2.noCalls lc = true ∧ noWbICall lc = true ∧ noMemEq lc = true ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 10 = some (val 10) ∧ blk.values[8]? = some 10 ∧
      (val 10).op = .ARM64FLDPQ ∧ (val 10).id = 10 ∧
      (constRo (symNames g)).isEmpty = true ∧ uL35 lc (uIn35 lc 1) blk 8 = [] ∧
      ((val 10).aux.bind (symOf? lc.ctx.tabs ·)).map (·.1.toStringLossy) =
        some "main..stmp_16" ∧
      (val 10).auxInt.toInt = 0 ∧
      (memT.read pT 16).isSome = true ∧ (memT.read pT16 16).isSome = true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 10))
        (fun s1 => isBlob blob0 s1.regs[31]? && isBlob blob1 s1.regs[32]?) = true := by
  have hf := g64_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none, decide_eq_true_eq, List.all_eq_true] at hf
  obtain ⟨hl, hres, h63, hlt, hav, hvo, hact, hsl, hfo, h48, hnc, hwi, hme, hm1, hbs, hvs, hi8,
    hop, hid, hro, hu0, hsy, hoff, hr0, hr1, hrun⟩ := hf
  refine ⟨hl, ?_, h63, hlt, hav, hvo, hact, hsl, hfo, h48, hnc, hwi, hme, hm1, ?_, ?_, hi8, hop,
    hid, hro, hu0, hsy, hoff, hr0, hr1, hrun⟩
  · revert hres; cases checkG64 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem ι_glob (name : String) : ι (.global name) = some GenG2.symA := rfl

theorem addrAgree : AddrAgree ι := by
  intro b n a hb ha _
  cases b <;> simp [ι, Blk.base?, Blk.fixedBase?] at ha hb <;> (try subst hb) <;> (try subst ha) <;>
    first | rfl | (obtain ⟨_, rfl, rfl⟩ := ha; rfl)

theorem envT (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hav : accessedVars lc = [3])
    (hvo : varOp g 3 = some (.PARAM, 0)) (hact : lc.ctx.act = 0)
    (hsl : (homeSlots lc).isEmpty = true) (hoff : frameOff L .PARAM 0 = 8)
    (hnc : GenG2.noCalls lc = true) (hwi : noWbICall lc = true) (hme : noMemEq lc = true) :
    G49Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
            link := rfl
            pcOf := rfl
            retOut := fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := addrAgree
            glob := fun _ name _ _ => ι_glob name.toStringLossy
            syms := by
              intro y
              have hs : L.sym y = GenG2.symA := rfl
              rw [hs]
              refine ⟨by decide, fun p hp => ?_⟩
              exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
            calls := fun _ id v hv hop => by
              have h1 : lc.ctx.f.valueTab[id]? = some (some v) := by
                have hv' : (lc.ctx.f.valueTab[id]?).join = some v := hv
                cases h : lc.ctx.f.valueTab[id]? with
                | none => rw [h] at hv'; cases hv'
                | some o => rw [h] at hv'; cases o <;> simp_all
              have h2 := (Array.all_eq_true_iff_forall_mem.1 hnc) _ (Array.mem_of_getElem? h1)
              simp [hop] at h2
            slot := fun k hk => by simp [List.isEmpty_iff.1 hsl] at hk
            extra := by decide
            frame := ⟨by decide, by decide, fun k off h => by cases h⟩ }
          vars := by
            intro x hx o ho _
            rw [hav, List.mem_singleton] at hx
            subst hx
            rw [hvo] at ho
            cases ho }
        wbs := fun _ _ _ hv => (noWbICall_spec hwi hv).1 }
      icalls := fun _ _ _ hv => (noWbICall_spec hwi hv).2 }
    memeqs := fun _ _ _ hv => noMemEq_spec hme hv }
  vars := by
    intro x hx nc o ho _ _
    rw [hav, List.mem_singleton] at hx
    subst hx
    rw [hvo] at ho
    cases ho
    rw [hact, hoff]
    decide

/-! ## The memory and the state -/

theorem memT_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ memT.blocks) :
    b = .global "main..stmp_16" ∧ al = { data := bytesT, writable := false } := by
  simpa [memT] using h

/-- `memT` injected into `MT` by `ι`: `main..stmp_16`'s bytes at `symA`. -/
theorem memInjT : MemInj ι memT MT where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := memT_blocks h
    exact ⟨GenG2.symA, ι_glob _, fun _ => by decide, by simp [bytesT, GenG2.symA]⟩
  inj := by
    intro b al b' al' a a' h h' hne
    obtain ⟨rfl, -⟩ := memT_blocks h
    obtain ⟨rfl, -⟩ := memT_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    obtain ⟨rfl, rfl⟩ := memT_blocks h
    rw [ι_glob] at ha
    cases ha
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    have hi' : i < 40 := by simpa [bytesT] using hi
    have hd : (GenG2.symA + BitVec.ofNat 64 i - GenG2.symA).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    simp [ByteRel, MT, hd, hi', bytesT]

theorem keysT : KeysNodup memT := by simp [KeysNodup, memT]

theorem sepT : SepFrom ι (StkAt E) memT := by
  intro b al a _ _ y hy
  rcases hy with ⟨h, -⟩ | ⟨k, off, h, -⟩ <;> cases h

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) : x = .poison := by
  simp only [s0, Array.getElem?_replicate] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 8 m0 where
  regs := by
    intro r v hv
    rw [s0_regs hv]
    exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨memT, rfl, memInjT⟩
  frame := by
    refine ⟨rfl, rfl, fun h => ?_, fun _ => ⟨rfl, rfl⟩⟩
    cases h
  pc := rfl

theorem inv0 (K : KMap) : G3Inv E lc K s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, memT, rfl, keysT, sepT⟩
    rw [s0_regs hv]
    trivial
  slots := by intro k v h; simp [s0] at h

/-- G2's symbols have no float constant: `RoPre56` holds at `s0`. -/
theorem ro0 (hro : (constRo (symNames g)).isEmpty = true) : RoPre56 g s0 := by
  intro mm _
  rw [List.isEmpty_iff.1 hro]
  intro n a h
  cases h

/-! ## `v10`: `FLDPQ main..stmp_16(SB), (F0, F1)` -/

/-- The per-value premises of G54 on `v10`, `FLDPQ`: none of them applies. -/
theorem pre54 (hop : (val 10).op = .ARM64FLDPQ) : G54Pre lc s0 (val 10) := by
  have hne : ∀ o : Op, o ≠ .ARM64FLDPQ → (val 10).op ≠ o := fun o h h' => h (h'.symm.trans hop)
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

/-- `QLoadPre` on `v10`: it reads 16 valid bytes of `main..stmp_16` at 0 and at 16. -/
theorem preQ (hop : (val 10).op = .ARM64FLDPQ)
    (hsy : ((val 10).aux.bind (symOf? lc.ctx.tabs ·)).map (·.1.toStringLossy) =
      some "main..stmp_16")
    (hoff : (val 10).auxInt.toInt = 0)
    (hr0 : (memT.read pT 16).isSome = true) (hr1 : (memT.read pT16 16).isSome = true) :
    QLoadPre lc s0 (val 10) := by
  refine ⟨fun h => absurd (h.symm.trans hop) (by decide), fun _ a x _ _ => ?_⟩
  obtain ⟨y, hy, hsy'⟩ := Option.map_eq_some_iff.1 hsy
  obtain ⟨x', hx', hs'⟩ := Option.bind_eq_some_iff.1 hy
  obtain ⟨name, abi⟩ := y
  simp only at hsy'
  have hpq := pairAddr_globN (a := x) (n := 16) hx' hs'
  rw [hsy', hoff] at hpq
  have hp : (⟨.global "main..stmp_16", BitVec.ofInt 64 (0 : Int)⟩ : Ptr) = pT := by
    simp only [pT]; decide
  have hq : (⟨.global "main..stmp_16", BitVec.ofInt 64 (0 : Int) + BitVec.ofNat 64 16⟩ :
      Ptr) = pT16 := by
    simp only [pT16]; decide
  rw [hp, hq] at hpq
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hr0
  obtain ⟨bs', hbs'⟩ := Option.isSome_iff_exists.1 hr1
  exact ⟨pT, pT16, memT, bs, bs', hpq, rfl, hbs, hbs'⟩

/-- Two 128-bit vectors with the same 16 bytes are equal. -/
theorem bv128_ext {q Q : BitVec 128}
    (h : ∀ i < 16, q.extractLsb' (8 * i) 8 = Q.extractLsb' (8 * i) 8) : q = Q := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hk := congrArg (fun x : BitVec 8 => x.getLsbD (j % 8)) (h (j / 8) (by omega))
  have e : 8 * (j / 8) + j % 8 = j := by omega
  simpa [BitVec.getLsbD_extractLsb', Nat.mod_lt, e] using hk

/-- A V register holding a blob of 16 concrete bytes `f 0`, …, `f 15` (`VRel`'s `BlobRel`) is
the vector with those bytes. -/
theorem vRel_eq {ι' : Blk → Option (BitVec 64)} {bs : List Byte} {q Q : BitVec 128}
    {f : Nat → BitVec 8} (hb : bs = (List.range 16).map fun i => .b (f i))
    (hQ : ∀ i < 16, Q.extractLsb' (8 * i) 8 = f i) (h : VRel ι' (.blob bs) q) : q = Q := by
  have h' : BlobRel ι' bs q := h
  obtain ⟨-, hr⟩ := h'
  apply bv128_ext
  intro i hi
  have := hr i (by simp [hb, hi])
  simp only [hb, List.getElem_map, List.getElem_range, ByteRel] at this
  rw [hQ i hi]
  exact this.symm

theorem Q0_bytes : ∀ i < 16, Q0.extractLsb' (8 * i) 8 = byteT i := by decide

theorem Q1_bytes : ∀ i < 16, Q1.extractLsb' (8 * i) 8 = byteT (16 + i) := by decide

/-- `F0` and `F1` are Go registers 31 and 32, the obj registers `V0` and `V1`. -/
theorem objV31 : objV? 31 = some (BitVec.ofNat 5 0) := by decide

theorem objV32 : objV? 32 = some (BitVec.ofNat 5 1) := by decide

/-- **G64 on `makearray` of `test/range`** (`v10 = FLDPQ {main..stmp_16} [0] v3 v11`, the
128-bit pair load `FLDPQ main..stmp_16(SB), (F0, F1)` of the literal `[5]int{1, 2, 3, 4, 5}`):
`checkG63` rejects the function and `checkG64` accepts it. From a state whose memory holds the
literal, where `QLoadPre` holds (both 16-byte reads find valid bytes), `stepLoc` runs `v10` to the
blobs `blob0` (`1`, `2`) in `F0` and `blob1` (`3`, `4`) in `F1`, and `g64_value` (at the mode
`false`, the function needing no G48 mode) relates it to a machine run from `m0`, which holds the
literal at `symA`, to a state whose `V0` and `V1` are `Q0` and `Q1`, under an activation extending
`E` that is again a `G49Env`. -/
theorem genG64_witness :
    (checkG63 lc0 ps bs g).toOption = none ∧ (val 10).op = .ARM64FLDPQ ∧
      QLoadPre lc s0 (val 10) ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 10) = .ok s1 ∧
        s1.regs[31]? = some (.blob blob0) ∧ s1.regs[32]? = some (.blob blob1) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 9 m1 ∧ m1.v 0 = Q0 ∧ m1.v 1 = Q1 := by
  obtain ⟨hl, hc, h63, hlt, hav, hvo, hact, hsl, hfo, h48, hnc, hwi, hme, hm1, hb, hv10, hi8, hop,
    hid, hro, hu0, hsy, hoff, hr0, hr1, hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hr
  have hr31 := isBlob_spec hr.1
  have hr32 := isBlob_spec hr.2
  have hE := envT hlt hav hvo hact hsl hfo hnc hwi hme
  have hq := preQ hop hsy hoff hr0 hr1
  have hne : ∀ o : Op, o ≠ .ARM64FLDPQ → (val 10).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  -- `g64_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 10 = some (val 10) := by
    rw [← liveCtx_ctx (lc := lc0)]; exact hv10
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -, -⟩ := g64_value (H := GenG2.H0) (env := GenG2.env)
    (osp := false) hc hE hl0 hm0 hb0 hi8 hv0 (by rw [hop]; rfl) locMatch0 (inv0 _)
    (fun h => by cases h) (fun h => by cases h)
    (fun h => by
      have h' : needs48 lc = true := h
      rw [h48] at h'
      cases h')
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 8); rw [hu0]; intro e he; cases he)
    (pre54 hop) (ro0 hro)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide)))
    (fun h => by cases h) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hq hs1
  refine ⟨h63, hop, hq, s1, E1, m1, hs1, hr31, hr32, hx1, hE1, hp1, hm1', ?_, ?_⟩
  · exact vRel_eq rfl Q0_bytes ((hm1'.regs 31 _ hr31).2 _ objV31)
  · exact vRel_eq rfl Q1_bytes ((hm1'.regs 32 _ hr32).2 _ objV32)

end GoFV.Proof.Witness.GenG64
