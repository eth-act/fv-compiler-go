import GoFV.Proof.Gen.G20
import GoFV.Proof.Witness.GenG19

/-!
# Non-vacuity witness: slice G20 of the genssa validator on `runtime.NumCPU` (std/runtime)

`std/std/runtime/NumCPU,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`): `NumCPU`
(`runtime/debug.go`), `return int(ncpu)` with `ncpu int32` a global.

`checkG19` rejects it (`v8 = MOVDnop`); `checkG20` accepts it with the PC table `tab` and the class
table `kt`. Block `b1`: `v7 = MOVWload {ncpu} v3 v1` (`MOVW runtime.ncpu(SB), R0`, the sign
extension of the 4 bytes) and `v8 = MOVDnop v7` (no code, in `R0`), whose upper-bit table entry
`uAt lc blk1 3 = (R0, 32, signed)` comes from `v7`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g20_facts`),
`stepLoc` runs `v7` and `v8` from a state whose memory holds `ncpu = -2` (`memG`, the bytes
`fe ff ff ff`): `R0` then holds the 64-bit integer `-2` (`0xffff_ffff_ffff_fffe`), the sign
extension that `signOf v7` names. On a framed activation with `G10Env` (as `GenG18`'s, the globals at
`symA`) and the machine memory holding those bytes at `symA` (`MG`), `g20_value` runs the load
`MOVW runtime.ncpu(SB), R0`, which gives the upper-bit invariant `UOK` for `R0`, and then `MOVDnop`,
with no code: the machine's `X0` is `0xffff_ffff_ffff_fffe` (`genG20_value_witness`), which a zero
extension (`0x0000_0000_ffff_fffe`) would not be.
-/

namespace GoFV.Proof.Witness.GenG20

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/NumCPU,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "NumCPU" 1 0 0
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
type t2 INT 8 8 0 comparable,named "int" "int"
type t1 FUNC 8 8 8 hasptr,direct "func() int" "func() int" 0 0 1
field 0 "" t2 ? 0
aux a2 sym "runtime.NumCPU" "runtime.NumCPU" 1 - 0 - - - - 0
posbase p6 "runtime/debug.go" 1 1 -1
aux a3 name "~r0" "~r0" PPARAMOUT t2 0 1 - p6:154:15:0:0
aux a1 call "AuxCall{runtime.NumCPU}" a2 1 0 1 8 0 0 1
abiparam out 0 t2 a3 0 -1
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
aux a4 sym "runtime.numCPUStartup" "runtime.numCPUStartup" 0 - 0 - - - - 0
type t33 RESULTS ? ? ? - "int,mem" "" 2 t2,t28
f b1 t1 a1 9 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t2,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const64 t2 0 - p0:0:0:0:0 0 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:0:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts 0=v5
freev -
freeb -
dcllen 1
end
pass 1 "number lines"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const64 t2 0 - p0:0:0:0:0 0 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts 0=v5
freev -
freeb -
cache postorder b1
cache linestarts 6:155:155
dcllen 1
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const64 t2 0 - p0:0:0:0:0 0 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts 0=v5
freev -
freeb -
cache postorder b1
cache linestarts 6:155:155
dcllen 1
end
pass 3 "early deadcode"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache linestarts 6:155:155
dcllen 1
end
pass 4 "short circuit"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache linestarts 6:155:155
dcllen 1
end
pass 5 "decompose user"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache linestarts 6:155:155
dcllen 1
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache linestarts 6:155:155
dcllen 1
end
pass 7 "opt"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache linestarts 6:155:155
dcllen 1
end
pass 8 "zero arg cse"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache linestarts 6:155:155
dcllen 1
end
pass 9 "opt deadcode"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache linestarts 6:155:155
dcllen 1
end
pass 10 "generic cse"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 11 "phiopt"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 12 "gcse deadcode"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 13 "nilcheckelim"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 14 "prove"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 15 "divisible"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 16 "divmod"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 17 "middle opt"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 18 "known bits"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 19 "early fuse"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v5,v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 20 "expand calls"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
v v5 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t20 0 a3 p6:155:2:0:0 0 v5,v1
names -
splits -
canon -
consts -
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 21 "decompose builtin"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
v v5 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t20 0 a3 p6:155:2:0:0 0 v5,v1
names -
splits -
canon -
consts -
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 22 "softfloat"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
v v5 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t20 0 a3 p6:155:2:0:0 0 v5,v1
names -
splits -
canon -
consts -
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 23 "branchelim"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
v v5 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t20 0 a3 p6:155:2:0:0 0 v5,v1
names -
splits -
canon -
consts -
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 24 "late opt"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 25 "dead auto elim"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 26 "sccp"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 27 "generic deadcode"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 28 "late fuse"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 29 "check bce"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 30 "dse"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 31 "memcombine"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 32 "writebarrier"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Addr t18 0 a4 p0:0:0:0:0 1 v3
v v7 Load t6 0 - p6:155:13:1:0 1 v6,v1
v v8 SignExt32to64 t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 33 "lower"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVWreg t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 34 "addressing modes"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVWreg t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 35 "late lower"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 36 "pair"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 38 "lowered cse"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 39 "elim unread autos"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 41 "lowered deadcode"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 42 "checkLower"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 43 "loop invariant"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 45 "tighten"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 46 "late deadcode"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 47 "critical"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 48 "phi tighten"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 49 "likelyadjust"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 6:155:155
dcllen 1
end
pass 50 "layout"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 6:155:155
fstate laidout
dcllen 1
end
pass 51 "schedule"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 6:155:155
fstate scheduled,laidout
dcllen 1
end
pass 52 "late nilcheck"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 6:155:155
fstate scheduled,laidout
dcllen 1
end
pass 53 "flagalloc"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v6,v4,v5,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 6:155:155
fstate scheduled,laidout
dcllen 1
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.NumCPU}" a2 1 0 1 8 0 0 1
abiparam out 0 t2 a3 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v2,v4,v5,v6
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 6:155:155
fstate scheduled,laidout
regalloc 10 v3:SB,v7:R0,v8:R0,v9:[]
dcllen 1
end
pass 55 "loop rotate"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v2,v4,v5,v6
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 6:155:155
fstate scheduled,laidout
regalloc 10 v3:SB,v7:R0,v8:R0,v9:[]
dcllen 1
end
pass 56 "trim"
f b1 t1 a1 9 1
b b1 Ret p6:155:13:1:0 0 0 - v9 - -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v7 ARM64MOVWload t6 0 a4 p6:155:13:1:0 1 v3,v1
v v8 ARM64MOVDnop t2 0 - p6:155:13:0:0 1 v7
v v9 MakeResult t33 0 - p6:155:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v2,v4,v5,v6
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 6:155:155
fstate scheduled,laidout
regalloc 10 v3:SB,v7:R0,v8:R0,v9:[]
dcllen 1
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t21,t24,t25,t26,t27
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t2,t14,t15,t25,t26,t12,t13,t3,t17,t18,t19,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t33
eof
"#

/-- `std/std/runtime/NumCPU,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "NumCPU" 1
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
type t1 8 8 0 0 - "int"
name n1 "~r0" PPARAMOUT t1 1 "runtime.~r0" 0 a3
in n1 0 outregs
opt n1 0 outregs
stack 0 0 8
end
genin
posbase p6 "runtime/debug.go" 1 1 -1 5 "runtime/debug.go" "runtime/debug.go" 1 1
sym y1 "runtime.NumCPU" 1
curfn p6:154:6:0:0 0 0
regargs -
text y1 0 0 0 0 154 200080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.numCPUStartup" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i0 0 0 p6:154:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p6:154:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p6:154:6:0:0
p 3 3 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p6:155:13:1:0
p 4 4 0 0 0 - MOVW 0 MEM/0/0/0/EXTERN/0/0/y3/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p6:155:13:1:0
p 5 5 0 0 0 - RET 0 _ 0 - _ 0 0 p6:155:13:2:0
p 6 6 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 154 200080
funcaux y2 y2 - - - - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4
autot -
dbgentry 1
dbgregout n1
dbgpc -
end
asm
sym y4 "" 0
sym y5 "" 0
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i0 0 2 p6:154:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p6:154:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p6:154:6:0:0
p 3 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p6:155:13:1:0
p 4 0 0 0 397 - MOVW 0 MEM/0/0/0/EXTERN/110/0/y3/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p6:155:13:1:0
p 5 8 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p6:155:13:2:0
fn y1 0 0 0 0 154 2000c8
funcaux y2 y2 - - - - -
text 16 0 1b000090600380b9c0035fd600000000 1
reloc 0 8 R_ARM64_PCREL_LDST32 0 y3
pcln y5 y6 y7 y8 y4 y2,y2
usedfiles 5
data y2 Sxxx 0 4 8000 0100000000000000 0
data y4 SRODATA 3 1 28000 010400 0
data y5 SRODATA 3 1 28000 020400 0
data y6 SRODATA 3 1 28000 0c0400 0
data y7 SRODATA 4 1 28000 b8020400 0
data y8 SRODATA 3 1 28000 000400 0
end
dwarf
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "go:info.int" 0
sym y14 "type:int" 0
dwfn y9 y10 y11 - y12 "runtime.NumCPU" 5:154 1 0 1 4262
dwdcl -
dwclosure 0 -
dwparents -
dwparams n1
dwname n1 1 0 0 0 0 0 0 1 - - "int" 0 0 1 p6:154:15:0:0
var 0 0 "~r0" 5 1 1 0 0 0 y13 "runtime/debug.go" 154 15 0 0 0 0 -
scope 0 0 - 0
data y9 SDWARFFCN 42 0 0 0372756e74696d652e4e756d43505500000010019c060000009a01012e7e723000019a01000000000000 3
reloc 0 0 R_USETYPE 0 y14
reloc 16 2 R_DWTXTADDR_U2 0 y1
reloc 36 4 R_DWARFSECREF 0 y13
data y10 SDWARFLOC 0 0 0 - 0
data y11 SDWARFRANGE 0 0 0 - 0
data y12 SDWARFLINES 24 0 0 0009020000000000000000040603950114065f0208000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded `NumCPU` (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG20` gives (`b1`: the no-code `v3`, `v1`; `v7`'s `PCDATA` and `MOVW`; the
no-code `v8`, `v9`; `RET`). -/
def tab : PcTab := [(1, [3, 3, 3, 5, 5, 5])]

/-- The class table `checkG20` gives (nothing known at the entry). -/
def kt : KTab := (match checkG20 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG20`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The global `runtime.ncpu` (`int32`). -/
def pG : Ptr := ⟨.global "runtime.ncpu", 0⟩

/-- The bytes of `ncpu = -2`, little-endian. -/
def bytesG : Array Byte := #[.b 0xfe, .b 0xff, .b 0xff, .b 0xff]

/-- The Phase 1 memory: the global `runtime.ncpu` holding `-2`. -/
def memG : Mem := { blocks := #[(.global "runtime.ncpu", { data := bytesG })] }

/-- The machine memory: the bytes of `ncpu` at `symA`, 0 elsewhere. -/
def MG : Memory := fun y =>
  if (y - GenG2.symA).toNat < 4 then (if (y - GenG2.symA).toNat = 0 then 0xfe else 0xff) else 0

/-- The `runLoc` state before `v7`: every register `poison`, the memory `memG`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := memG },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem memG }

/-- The machine before `v7`: the activation's `g` and `FP`, the PC of `v7`, the memory `MG`. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := MG }

/-- A shape other than a boolean. -/
def notBool : Ty → Bool
  | .bool => false
  | _ => true

theorem notBool_spec {t : Ty} (h : notBool t = true) : t ≠ .bool := by
  rintro rfl; cases h

/-- `-2` as a 64-bit word. -/
def m2w : BitVec 64 := 0xfffffffffffffffe

/-- The register holds the 64-bit integer `m2w`. -/
def isM2 : Option Val → Bool
  | some (.int .w64 x) => decide (x = m2w)
  | _ => false

theorem isM2_spec {o : Option Val} (h : isM2 o = true) : o = some (.int .w64 m2w) := by
  unfold isM2 at h
  split at h
  · rw [of_decide_eq_true h]
  · cases h

/-- What compiled evaluation checks on `NumCPU`: `checkG20` accepts it with `tab` and `kt` and
`checkG19` does not; it accesses no frame variable and has no home slot; `b1` holds `v7`
(`MOVWload` of a global, not a boolean) at index 2 and `v8` (`MOVDnop`) at index 3, with nothing
in the upper-bit table before `v7`; `v7`'s address is `ncpu` and `memG` reads 4 bytes there;
`stepLoc` runs `v7` and `v8` from `s0` to `R0 = -2` as a 64-bit integer; and that word is no
pointer. -/
def gFacts : Bool :=
  (checkG20 lc ps bs g).toOption == some (tab, kt) && (checkG19 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 7).isSome && (lc.ctx.f.value? 8).isSome &&
    blk1.values[2]? == some 7 && blk1.values[3]? == some 8 &&
    (val 7).op == .ARM64MOVWload && (val 8).op == .ARM64MOVDnop && uAt lc blk1 2 == none &&
    (val 7).aux.isSome && decide (symAddr lc.ctx (val 7) .poison = some pG) &&
    (memG.read pG 4).isSome && notBool (lc.ty (val 7).id) &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 7)) (fun s1 =>
      GenG1.okThen (stepLoc GenG2.env lc s1 (val 8)) fun s2 =>
        isM2 s2.regs[0]?) &&
    decide ((Ptr.ofAddr m2w).blk = .nil)

theorem g20_facts : gFacts = true := by
  native_decide

/-- The facts of `g20_facts` as hypotheses. -/
theorem facts :
    checkG20 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 1 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 1 = some blk1 ∧ lc.ctx.f.value? 7 = some (val 7) ∧
      lc.ctx.f.value? 8 = some (val 8) ∧ blk1.values[2]? = some 7 ∧ blk1.values[3]? = some 8 ∧
      (val 7).op = .ARM64MOVWload ∧ (val 8).op = .ARM64MOVDnop ∧ uAt lc blk1 2 = none ∧
      (val 7).aux.isSome = true ∧ symAddr lc.ctx (val 7) .poison = some pG ∧
      (memG.read pG 4).isSome = true ∧ lc.ty (val 7).id ≠ .bool ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 7)) (fun s1 =>
        GenG1.okThen (stepLoc GenG2.env lc s1 (val 8)) fun s2 =>
          isM2 s2.regs[0]?) = true ∧
      (Ptr.ofAddr m2w).blk = .nil := by
  have hf := g20_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem,
    decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hm1⟩, hb1s⟩, hv7s⟩, hv8s⟩, hi2⟩, hi3⟩, hop7⟩,
    hop8⟩, hu⟩, hax⟩, hsym⟩, hrd⟩, hty⟩, hrun⟩, hnil⟩ := hf
  refine ⟨?_, hav, hsl, hm1, ?_, ?_, ?_, hi2, hi3, hop7, hop8, hu, hax, hsym, hrd,
    notBool_spec hty, hrun, hnil⟩
  · revert hres; cases checkG20 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [blk1, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv7s
    simp [val, hv]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv8s
    simp [val, hv]

theorem g20Env (hc : checkG20 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG20_spec hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := GenG12.addrAgree
        glob := fun _ _ _ _ => rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG20_spec hc
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

theorem memG_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ memG.blocks) :
    b = .global "runtime.ncpu" ∧ al = { data := bytesG } := by
  simpa [memG] using h

/-- `memG` injected into `MG` by `ι`: `ncpu`'s bytes at `symA`. -/
theorem memInjG : MemInj GenG12.ι memG MG where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := memG_blocks h
    exact ⟨GenG2.symA, rfl, fun _ => by decide, by simp [bytesG, GenG2.symA]⟩
  inj := by
    intro b al b' al' a a' h h' hne
    obtain ⟨rfl, -⟩ := memG_blocks h
    obtain ⟨rfl, -⟩ := memG_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    obtain ⟨rfl, rfl⟩ := memG_blocks h
    have ha' : a = GenG2.symA := by simp [GenG12.ι] at ha; exact ha.symm
    subst ha'
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    have hi4 : i < 4 := by simpa [bytesG] using hi
    have hd : (GenG2.symA + BitVec.ofNat 64 i - GenG2.symA).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    simp only [ByteRel, MG, hd, hi4, ↓reduceIte]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem keysG : KeysNodup memG := by simp [KeysNodup, memG]

theorem sepG : SepFrom GenG12.ι (StkAt E) memG := by
  intro b al a h ha y hy
  obtain ⟨rfl, rfl⟩ := memG_blocks h
  have ha' : a = GenG2.symA := by simp [GenG12.ι] at ha; exact ha.symm
  subst ha'
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    have hA : GenG2.symA.toNat = 0x10000000000 := rfl
    rw [hsp] at h2
    simp only [hA, bytesG, List.size_toArray, List.length_cons, List.length_nil]
    omega
  · cases hk

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) : x = .poison := by
  simp only [s0, Array.getElem?_replicate] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 2 m0 where
  regs := by
    intro r v hv
    rw [s0_regs hv]
    exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨memG, rfl, memInjG⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, MG, E]; decide,
    by simp only [MState.word, readMem, m0, MG, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g20Inv0 {K : KMap} : G3Inv E lc K s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, memG, rfl, keysG, sepG⟩
    rw [s0_regs hv]
    trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v7`, the global load: its address is `ncpu`, where `memG` reads 4
bytes; it is no compare, subtraction, pair load, nil check, zeroing or register-index load. -/
theorem pre7 (hop : (val 7).op = .ARM64MOVWload) (hax : (val 7).aux.isSome = true)
    (hsym : symAddr lc.ctx (val 7) .poison = some pG) (hrd : (memG.read pG 4).isSome = true)
    (hty : lc.ty (val 7).id ≠ .bool) : G14Pre lc s0 (val 7) := by
  have hne : ∀ o : Op, o ≠ .ARM64MOVWload → (val 7).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  have hsymx : ∀ x, symAddr lc.ctx (val 7) x = some pG := by
    intro x
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hax
    rw [← hsym]
    unfold symAddr
    rw [hn]
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hrd
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  rotate_left
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl
  intro as n sg hl a x _ _
  rw [hop] at hl
  cases hl
  exact ⟨pG, memG, bs, hsymx x, rfl, hbs, fun h => absurd h hty⟩

/-- The per-value premises of `v8`, `MOVDnop`: none apply. -/
theorem pre8 {s : LocState} (hop : (val 8).op = .ARM64MOVDnop) : G14Pre lc s (val 8) := by
  have hne : ∀ o : Op, o ≠ .ARM64MOVDnop → (val 8).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G20 on `NumCPU`**: from the state before `v7` with `ncpu = -2` (`memG`, at `symA` in `MG`),
`g20_value` runs the sign-extending load `MOVW runtime.ncpu(SB), R0` (`v7`), which establishes the
upper-bit invariant for `R0`, and then `MOVDnop` (`v8`, no code): `runLoc`'s `R0` holds the 64-bit
integer `-2` and the machine state, related to it before `v9` under an activation extending `E`,
has `X0 = 0xffff_ffff_ffff_fffe`, the sign extension of the loaded word. -/
theorem genG20_value_witness :
    ∃ s1 s2 E' m', stepLoc GenG2.env lc s0 (val 7) = .ok s1 ∧
      stepLoc GenG2.env lc s1 (val 8) = .ok s2 ∧ s2.regs[0]? = some (.int .w64 m2w) ∧
      E.Extends E' ∧ G10Env lc g L ps 0 tab E' ∧ PStar GenG2.H0 L ps.toList 0 m0 m' ∧
      LocMatch E' s2 1 4 m' ∧ m'.x 0 = m2w := by
  obtain ⟨hc, hav, hsl, hm1, hb, hv7, hv8, hi2, hi3, hop7, hop8, hu, hax, hsym, hrd, hty, hrun,
    hnil⟩ := facts
  obtain ⟨s1, hs1, h2⟩ := GenG1.okThen_spec hrun
  obtain ⟨s2, hs2, hr0⟩ := GenG1.okThen_spec h2
  have hr0' : s2.regs[0]? = some (.int .w64 m2w) := isM2_spec hr0
  have hE := g20Env hc hav hsl
  have hne7 : ∀ o : Op, o ≠ .ARM64MOVWload → (val 7).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop7)
  have hne8 : ∀ o : Op, o ≠ .ARM64MOVDnop → (val 8).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop8)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', hinv1, hu1⟩ := g20_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm1 hb hi2 hv7 (by rw [hop7]; rfl) locMatch0 g20Inv0 (by rw [hu]; trivial)
    (pre7 hop7 hax hsym hrd hty)
    (fun h => absurd h (hne7 _ (by decide))) (fun h => absurd h (hne7 _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop7]; rfl))
    (fun h => absurd h (hne7 _ (by decide))) (fun h => absurd h (hne7 _ (by decide)))
    (fun h => absurd h (hne7 _ (by decide))) hs1
  obtain ⟨E2, m2, hx2, hE2, hp2, hm2', -, -⟩ := g20_value (H := GenG2.H0) (env := GenG2.env)
    hc hE1 hm1 hb hi3 hv8 (by rw [hop8]; rfl) hm1' hinv1 hu1 (pre8 hop8)
    (fun h => absurd h (hne8 _ (by decide))) (fun h => absurd h (hne8 _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop8]; rfl))
    (fun h => absurd h (hne8 _ (by decide))) (fun h => absurd h (hne8 _ (by decide)))
    (fun h => absurd h (hne8 _ (by decide))) hs2
  refine ⟨s1, s2, E2, m2, hs1, hs2, hr0', MatchEnv.Extends.trans hx1 hx2, hE2, hp1.trans hp2,
    hm2', ?_⟩
  rcases (hm2'.regs 0 _ hr0').1 0 rfl with h | ⟨hn, -⟩
  · exact h
  · exact absurd hnil hn

end GoFV.Proof.Witness.GenG20
