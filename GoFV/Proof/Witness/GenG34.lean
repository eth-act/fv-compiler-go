import GoFV.Proof.Gen.G34
import GoFV.Proof.Witness.GenG13

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G34 of the genssa validator on `test/atomicload`'s `f`

`test/atomicload/main/f,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`;
`test/atomicload.go`):

```go
func f(p *byte) bool {
	x := *p
	a := int64(int8(x))
	b := int64(uint8(x))
	return a == b
}
```

Block `b1` (the entry): `v6 = ArgIntReg` (`p`, `R0`), `InitMem`, `v9 = MOVBUload v6` (`x`,
`MOVBU (R0), R1`), `v11 = MOVBreg v9` (`a`, `MOVB R1, R2`), `v13 = MOVDreg v9` (`b`, in place in
`R1`), `v7 = CMP v13 v11`, `v14 = Equal v7`, `MakeResult`. Before `v11` (index 3), G31's table
`uL31` and G34's `uL34` are both `[(1, 8, false)]`: `R1` is zero-extended from 8 bits. G31 does not
keep the table across `MOVBreg`, so `uL31` is empty before `v13` and `checkG33` rejects the function
(`MOVDnop/MOVDreg: upper bits unknown`); `keep34` keeps `R1`'s entry across `v11`, which writes
only `R2`, and `checkG34` accepts the function with the PC table `tab` and the class table `kt`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g34_facts`),
`stepLoc` runs `v11` from a state with the byte `x = 0xbe` in `R1` to `R2 = 0xffffffffffffffbe` (the
64-bit sign extension), keeping `R1 = 0xbe` (8 bits). On a framed activation with `G28Env`,
`g34_value` runs `MOVB R1, R2` (`genG34_witness`): the machine's `X2` is `0xffffffffffffffbe`, and
G34's table after `v11` gives the whole `X1 = 0xbe` (`LocMatch` alone gives only its low 8 bits).
-/

namespace GoFV.Proof.Witness.GenG34

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/atomicload/main/f,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "f" 1 0 0
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
type t3 UINT8 1 1 0 comparable,named "byte" "uint8"
type t2 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t3
type t4 BOOL 1 1 0 comparable,named "bool" "bool"
type t1 FUNC 8 8 8 hasptr,direct "func(*byte) bool" "func(*uint8) bool" 0 1 1
field 0 "p" t2 ? 0
field 1 "" t4 ? 0
aux a2 sym "main.f" "main.f" 1 - 0 - - - - 0
posbase p2 "./atomicload.go" 1 1 -1
aux a3 name "p" "p" PPARAM t2 0 1 used p2:14:8:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t4 0 1 - p2:14:17:0:0
aux a1 call "AuxCall{main.f}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t4 a4 0 -1
type t5 INT8 1 1 0 comparable,named "int8" "int8"
type t6 INT16 2 2 0 comparable,named "int16" "int16"
type t7 INT32 4 4 0 comparable,named "int32" "int32"
type t8 INT64 8 8 0 comparable,named "int64" "int64"
type t9 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t10 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t11 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t12 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t13 INT 8 8 0 comparable,named "int" "int"
type t14 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t15 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t16 UINT 8 8 0 comparable,named "uint" "uint"
type t17 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t18 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t9
type t20 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t7
type t21 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t11
type t22 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t13
type t23 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t17
type t24 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t14
type t25 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t15
type t26 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t19
type t27 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t28 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t29 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t30 SSA ? ? ? - "mem" ""
type t31 SSA ? ? ? - "flags" ""
type t32 SSA ? ? ? - "void" ""
type t33 SSA 16 8 ? - "int128" ""
type t34 RESULTS ? ? ? - "mem" "" 1 t30
type t35 PTR 8 8 8 hasptr,direct,comparable "**byte" "**uint8" t2
type t36 PTR 8 8 8 hasptr,direct,comparable "*bool" "*bool" t4
type t37 RESULTS ? ? ? - "bool,mem" "" 2 t4,t30
slot s1 a3 t2 0 - 0
aux a5 name "x" "x" PAUTO t3 0 1 used p2:15:2:0:0
slot s2 a5 t3 0 - 0
aux a6 name "a" "a" PAUTO t8 0 1 used p2:16:2:0:0
slot s3 a6 t8 0 - 0
aux a7 name "b" "b" PAUTO t8 0 1 used p2:17:2:0:0
slot s4 a7 t8 0 - 0
f b1 t1 a1 15 1
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t8,UInt8=t9,UInt16=t10,UInt32=t11,UInt64=t12,Int=t13,Float32=t14,Float64=t15,UInt=t16,Uintptr=t17,String=t18,BytePtr=t19,Int32Ptr=t20,UInt32Ptr=t21,IntPtr=t22,UintptrPtr=t23,Float32Ptr=t24,Float64Ptr=t25,BytePtrPtr=t26,Complex64=t27,Complex128=t28,UnsafePtr=t29,Mem=t30,Flags=t31,Void=t32,Int128=t33,ResultMem=t34
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v7 ConstBool t4 0 - p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p2:15:7:0:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v10 Copy t5 0 - p2:16:18:2:0 1 v9
v v11 SignExt8to64 t8 0 - p2:16:17:0:0 1 v10
v v12 Copy t9 0 - p2:17:19:2:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:0:0 1 v12
v v14 Eq64 t4 0 - p2:18:11:0:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v7
freev -
freeb -
dcllen 5
end
pass 1 "number lines"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v7 ConstBool t4 0 - p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v10 Copy t5 0 - p2:16:18:2:0 1 v9
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v10
v v12 Copy t9 0 - p2:17:19:2:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v12
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:15:18
dcllen 5
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v7 ConstBool t4 0 - p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 4 v8,v1
v v10 Copy t5 0 - p2:16:18:2:0 0 v9
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v12 Copy t9 0 - p2:17:19:2:0 0 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:15:18
dcllen 5
end
pass 3 "early deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:15:18
dcllen 5
end
pass 4 "short circuit"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:15:18
dcllen 5
end
pass 5 "decompose user"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:15:18
dcllen 5
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:15:18
dcllen 5
end
pass 7 "opt"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:15:18
dcllen 5
end
pass 8 "zero arg cse"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:15:18
dcllen 5
end
pass 9 "opt deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:15:18
dcllen 5
end
pass 10 "generic cse"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 11 "phiopt"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 12 "gcse deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 13 "nilcheckelim"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 14 "prove"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 15 "divisible"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 16 "divmod"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 17 "middle opt"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 18 "known bits"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 19 "early fuse"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v10,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 20 "expand calls"
aux a8 nameoff "p+0" a3 0
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v12 SB t17 0 - p0:0:0:0:0 0 -
v v10 SP t17 0 - p0:0:0:0:0 2 -
v v7 OffPtr t35 0 - p0:0:0:0:0 0 v10
v v5 LocalAddr t36 0 a4 p2:18:2:0:0 0 v10,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v7
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 21 "decompose builtin"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v12 SB t17 0 - p0:0:0:0:0 0 -
v v10 SP t17 0 - p0:0:0:0:0 2 -
v v7 OffPtr t35 0 - p0:0:0:0:0 0 v10
v v5 LocalAddr t36 0 a4 p2:18:2:0:0 0 v10,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v7
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 22 "softfloat"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v12 SB t17 0 - p0:0:0:0:0 0 -
v v10 SP t17 0 - p0:0:0:0:0 2 -
v v7 OffPtr t35 0 - p0:0:0:0:0 0 v10
v v5 LocalAddr t36 0 a4 p2:18:2:0:0 0 v10,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v7
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 23 "branchelim"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v12 SB t17 0 - p0:0:0:0:0 0 -
v v10 SP t17 0 - p0:0:0:0:0 2 -
v v7 OffPtr t35 0 - p0:0:0:0:0 0 v10
v v5 LocalAddr t36 0 a4 p2:18:2:0:0 0 v10,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v7
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 24 "late opt"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v7,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 25 "dead auto elim"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v7,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 26 "sccp"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v7,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 27 "generic deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v7,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 28 "late fuse"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v7,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 29 "check bce"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v7,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 30 "dse"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v7,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 31 "memcombine"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v7,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 32 "writebarrier"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 NilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 Load t3 0 - p2:15:7:0:0 2 v8,v1
v v11 SignExt8to64 t8 0 - p2:16:17:1:0 1 v9
v v13 ZeroExt8to64 t8 0 - p2:17:18:1:0 1 v9
v v14 Eq64 t4 0 - p2:18:11:1:0 1 v11,v13
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v7,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 33 "lower"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVBUreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 34 "addressing modes"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVBUreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 35 "late lower"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 36 "pair"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:15:18
dcllen 5
end
pass 38 "lowered cse"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
dcllen 5
end
pass 39 "elim unread autos"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
dcllen 5
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
dcllen 5
end
pass 41 "lowered deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
dcllen 5
end
pass 42 "checkLower"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
dcllen 5
end
pass 43 "loop invariant"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
dcllen 5
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
dcllen 5
end
pass 45 "tighten"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
dcllen 5
end
pass 46 "late deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
dcllen 5
end
pass 47 "critical"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
dcllen 5
end
pass 48 "phi tighten"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
dcllen 5
end
pass 49 "likelyadjust"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
dcllen 5
end
pass 50 "layout"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:15:7:1:0 1 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v8,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
fstate laidout
dcllen 5
end
pass 51 "schedule"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v8 ARM64LoweredNilCheck t32 0 - p2:15:7:1:0 0 v6,v1
v v9 ARM64MOVBUload t3 0 - p2:15:7:0:0 2 v6,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
fstate scheduled,laidout
dcllen 5
end
pass 52 "late nilcheck"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v9 ARM64MOVBUload t3 0 - p2:15:7:1:0 2 v6,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
fstate scheduled,laidout
dcllen 5
end
pass 53 "flagalloc"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v9 ARM64MOVBUload t3 0 - p2:15:7:1:0 2 v6,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v5,v10,v12,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
fstate scheduled,laidout
dcllen 5
end
pass 54 "regalloc"
aux a1 call "AuxCall{main.f}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t4 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v9 ARM64MOVBUload t3 0 - p2:15:7:1:0 2 v6,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v2,v3,v4,v5,v10,v12
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
fstate scheduled,laidout
regalloc 16 v6:R0,v9:R1,v11:R2,v13:R1,v14:R0,v15:[]
dcllen 5
end
pass 55 "loop rotate"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v9 ARM64MOVBUload t3 0 - p2:15:7:1:0 2 v6,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v2,v3,v4,v5,v10,v12
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
fstate scheduled,laidout
regalloc 16 v6:R0,v9:R1,v11:R2,v13:R1,v14:R0,v15:[]
dcllen 5
end
pass 56 "trim"
f b1 t1 a1 15 1
b b1 Ret p2:18:11:1:0 0 0 - v15 - -
v v6 ArgIntReg t2 0 a8 p2:18:11:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v9 ARM64MOVBUload t3 0 - p2:15:7:1:0 2 v6,v1
v v11 ARM64MOVBreg t8 0 - p2:16:17:1:0 1 v9
v v13 ARM64MOVDreg t8 0 - p2:17:18:1:0 1 v9
v v7 ARM64CMP t31 0 - p2:18:11:1:0 1 v13,v11
v v14 ARM64Equal t4 0 - p2:18:11:1:0 1 v7
v v15 MakeResult t37 0 - p2:18:2:0:0 1 v14,v1
names s1,s2,s3,s4
named s1 v6
named s2 v9
named s3 v11
named s4 v13
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v2,v3,v4,v5,v10,v12
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 2:15:18
fstate scheduled,laidout
regalloc 16 v6:R0,v9:R1,v11:R2,v13:R1,v14:R0,v15:[]
dcllen 5
end
frontend
end
ptrcache t2,t3,t6,t7,t8,t9,t11,t13,t14,t15,t17,t18,t19,t26
typelink t2=t19,t3=t9,t26=t35,t30=t34
typeorder t5,t3=t9,t6,t10,t7,t11,t8,t12,t13,t16,t17,t27,t28,t14,t15,t4,t2=t19,t20,t21,t22,t23,t24,t25,t36,t26=t35,t1,t18,t29,t30,t32,t31,t33,t34,t37
eof
"#

/-- `test/atomicload/main/f,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "f" 1
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
type t1 8 8 8 1 01 "*byte"
name n1 "p" PPARAM t1 1 "main.p" 0 a3
type t2 1 1 0 0 - "bool"
name n2 "~r0" PPARAMOUT t2 1 "main.~r0" 0 a4
type t3 1 1 0 0 - "byte"
name n3 "x" PAUTO t3 1 "main.x" 0 a5
type t4 8 8 0 0 - "int64"
name n4 "a" PAUTO t4 1 "main.a" 0 a6
name n5 "b" PAUTO t4 1 "main.b" 0 a7
in n1 0 used
in n2 0 outregs
in n3 0 used
in n4 0 used
in n5 0 used
out n1 0 used
opt n4 0 -
opt n5 0 -
opt n3 0 -
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p2 "./atomicload.go" 1 1 -1 1 "./atomicload.go" "./atomicload.go" 1 1
sym y1 "main.f" 1
curfn p2:14:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 14 201080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "main.f.arginfo1" 0
sym y5 "main.f.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:14:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:14:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:14:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:14:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:14:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:14:6:2:0
p 6 6 0 0 0 - MOVBU 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:15:7:1:0
p 7 7 0 0 0 - MOVB 0 REG/8193/0/0/NONE/0/0/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p2:16:17:1:0
p 8 8 0 0 0 - CMP 0 REG/8194/0/0/NONE/0/0/-/- 8193 - _ 0 0 p2:18:11:1:0
p 9 9 0 0 0 - CSET 0 SPECIAL/0/0/0/NONE/0/128/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:18:11:2:0
p 10 10 0 0 0 - RET 0 _ 0 - _ 0 0 p2:18:11:2:0
p 11 11 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 14 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgslot 1 n3 t3 0
dbgslot 2 n4 t4 0
dbgslot 3 n5 t4 0
dbgvar 0 n1 0
dbgvar 1 n3 1
dbgvar 2 n4 2
dbgvar 3 n5 3
dbgloc 0 1:-10000:1:14:50
dbgloc 1 1:9:1:13:51
dbgloc 2 1:11:-1:-30000:52
dbgloc 3 1:13:-1:-30000:51
dbgregout n2
dbgpc 1:14:10,1:9:7,1:13:8,1:11:8
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p2:14:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:14:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:14:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:14:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p2:14:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:14:6:2:0
p 6 0 0 0 294 - MOVBU 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:15:7:1:0
p 7 4 0 0 276 - MOVB 0 REG/8193/0/0/NONE/2/0/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p2:16:17:1:0
p 8 8 0 0 92 - CMP 0 REG/8194/0/0/NONE/2/0/-/- 8193 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:18:11:1:0
p 9 12 0 0 103 - CSET 0 SPECIAL/0/0/0/NONE/11/128/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:18:11:2:0
p 10 16 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:18:11:2:0
fn y1 8 0 0 0 14 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 32 0 01004039221c40933f0002ebe0179f9ac0035fd6000000000000000000000000 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y3,_,_,_,y4,y5
usedfiles 1
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 040800 0
data y10 SRODATA 3 1 28000 020800 0
data y11 SRODATA 3 1 28000 040800 0
data y12 SRODATA 7 1 28000 20010201040600 0
data y13 SRODATA 3 1 28000 000800 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.main.f$abstract" 0
sym y18 "" 0
sym y19 "go:info.*uint8" 0
sym y20 "go:info.bool" 0
sym y21 "go:info.uint8" 0
sym y22 "go:info.int64" 0
sym y23 "type:bool" 0
dwfn y14 y15 y16 y17 y18 "main.f" 1:14 1 0 1 4
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y17 n1,n2,n3,n4,n5
dwname n1 1 1 0 0 0 0 0 0 - - "*uint8" 0 0 1 p2:14:8:0:0
dwname n4 1 0 0 0 0 0 0 0 - - "int64" 0 0 1 p2:16:2:0:0
dwname n5 1 0 0 0 0 0 0 0 - - "int64" 0 0 1 p2:17:2:0:0
dwname n3 1 0 0 0 0 0 0 0 - - "uint8" 0 0 1 p2:15:2:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "bool" 0 0 1 p2:14:17:0:0
var 0 0 "p" 5 1 0 0 0 8 y19 "./atomicload.go" 14 8 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y20 "./atomicload.go" 14 17 0 1 0 0 -
var 2 0 "x" 52 1 0 0 0 -8 y21 "./atomicload.go" 15 2 0 2 1 0 v1
var 3 0 "a" 52 1 0 0 0 -8 y22 "./atomicload.go" 16 2 0 3 1 0 v2
var 4 0 "b" 52 1 0 0 0 -8 y22 "./atomicload.go" 17 2 0 4 1 0 v3
scope 0 0 - 0,1,2,3,4
dieref y14 3 y17 0
dieref y14 6 y17 2
dieref y14 8 y17 3
dieref y14 10 y17 4
dieoff y17 0:11,2:19,3:27,4:35
data y14 SDWARFFCN 58 0 0 06000000000020019c2900000000000000002e7e723000010e000000000023000000000000000023000000000000000023000000000000000000 12
reloc 0 0 R_USETYPE 0 y23
reloc 1 4 R_DWARFSECREF 0 y17
reloc 5 1 R_DWTXTADDR_U1 0 y1
reloc 10 4 R_DWARFSECREF 0 y17
reloc 14 4 R_DWARFSECREF 0 y15
reloc 25 4 R_DWARFSECREF 0 y20
reloc 31 4 R_DWARFSECREF 0 y17
reloc 35 4 R_DWARFSECREF 8 y15
reloc 40 4 R_DWARFSECREF 0 y17
reloc 44 4 R_DWARFSECREF 16 y15
reloc 49 4 R_DWARFSECREF 0 y17
reloc 53 4 R_DWARFSECREF 24 y15
data y15 SDWARFLOC 32 0 0 0100040010015000010004040801510001000408200152000100040820015100 4
reloc 1 1 R_DWTXTADDR_U1 0 y1
reloc 9 1 R_DWTXTADDR_U1 0 y1
reloc 17 1 R_DWTXTADDR_U1 0 y1
reloc 25 1 R_DWTXTADDR_U1 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y18 SDWARFLINES 25 0 0 00090200000000000000000402030914383906370214000101 1
reloc 3 8 R_ADDR 0 y1
data y17 SDWARFABSFCN 44 0 1 056d61696e2e6600010e0122700000000000002178000f000000002161001000000000216200110000000000 4
reloc 15 4 R_DWARFSECREF 0 y19
reloc 23 4 R_DWARFSECREF 0 y21
reloc 31 4 R_DWARFSECREF 0 y22
reloc 39 4 R_DWARFSECREF 0 y22
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

/-- The PC table `checkG34` gives (`b1`: one entry per value `v6`, `v1`, `v9`, `v11`, `v13`, `v7`,
`v14`, `v15`, then the `RET`). -/
def tab : PcTab := [(1, [5, 5, 5, 7, 8, 8, 9, 10, 10])]

/-- The class table `checkG34` gives. -/
def kt : KTab := (match checkG34 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG34`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The empty memory. -/
def mem0 : Mem := {}

theorem memInj0 (mm : Memory) : MemInj GenG12.ι mem0 mm where
  nil := rfl
  mapped := by intro b al h; simp [mem0] at h
  inj := by intro b al b' al' a a' h; simp [mem0] at h
  bytes := ⟨fun _ _ => False, by intro b al a h; simp [mem0] at h⟩

/-- The `runLoc` state before `v11`: the byte `x = 0xbe` (`v9`) in `R1`, every other register
`poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 1 then .int .w8 0xbe else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v11`: `X1 = 0xbe`, zero-extended from 8 bits, the activation's `g` and
`FP`, the PC of `v11`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 1 then 0xbe else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 3, mem := fun _ => 0 }

/-- The register holds the 64-bit integer `0xffffffffffffffbe`. -/
def isW64 : Option Val → Bool
  | some (.int .w64 x) => x == 0xffffffffffffffbe
  | _ => false

theorem isW64_spec {o : Option Val} (h : isW64 o = true) :
    o = some (.int .w64 0xffffffffffffffbe) := by
  unfold isW64 at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- The register holds the 8-bit integer `0xbe`. -/
def isW8 : Option Val → Bool
  | some (.int .w8 x) => x == 0xbe
  | _ => false

theorem isW8_spec {o : Option Val} (h : isW8 o = true) : o = some (.int .w8 0xbe) := by
  unfold isW8 at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on `f`: it holds an arm64 op, `checkG34` accepts it with `tab`
and `kt` and `checkG33` does not; it accesses no frame variable and has no home slot; `b1` is the
entry (`uIn34 lc 1 = []`) and holds `v11` (`MOVBreg v9`) at index 3 and `v13` (`MOVDreg v9`) at
index 4; `R1` has class 8 before `v11`, where G34's table is `[(1, 8, false)]`; after `v11`, G31's
table `uL31` is empty while G34's is still `[(1, 8, false)]`; `stepLoc` runs `v11` from `s0` to
`R2 = 0xffffffffffffffbe` (64 bits), keeping `R1 = 0xbe` (8 bits). -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG34 lc ps bs g).toOption == some (tab, kt) && (checkG33 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 11).isSome && blk.values[3]? == some 11 && blk.values[4]? == some 13 &&
    (val 11).op == .ARM64MOVBreg && (val 11).args == #[9] &&
    (val 13).op == .ARM64MOVDreg && (val 13).args == #[9] &&
    (kAt lc kt 1 blk 3).get 1 == some 8 &&
    uIn34 lc 1 == [] && uL34 lc (uIn34 lc 1) blk 3 == [(1, 8, false)] &&
    uL31 lc (uIn lc 1) blk 4 == [] && uL34 lc (uIn34 lc 1) blk 4 == [(1, 8, false)] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 11)) fun s1 => isW64 s1.regs[2]? && isW8 s1.regs[1]?

theorem g34_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG34 lc ps bs g = .ok (tab, kt) ∧
      (checkG33 lc ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 11 = some (val 11) ∧ blk.values[3]? = some 11 ∧ blk.values[4]? = some 13 ∧
      (val 11).op = .ARM64MOVBreg ∧ (val 11).args = #[9] ∧
      (val 13).op = .ARM64MOVDreg ∧ (val 13).args = #[9] ∧
      (kAt lc kt 1 blk 3).get 1 = some 8 ∧
      uIn34 lc 1 = [] ∧ uL34 lc (uIn34 lc 1) blk 3 = [(1, 8, false)] ∧
      uL31 lc (uIn lc 1) blk 4 = [] ∧ uL34 lc (uIn34 lc 1) blk 4 = [(1, 8, false)] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 11))
        (fun s1 => isW64 s1.regs[2]? && isW8 s1.regs[1]?) = true := by
  have hf := g34_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h33, hav, hsl, hm1, hbs, hvs, hi3, hi4, hop, hargs, hop13, hargs13, hk1, hin,
    hu3, hu31, hu4, hrun⟩ := hf
  refine ⟨hl, ?_, h33, hav, hsl, hm1, ?_, ?_, hi3, hi4, hop, hargs, hop13, hargs13, hk1, hin, hu3,
    hu31, hu4, hrun⟩
  · revert hres; cases checkG34 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g34Env (hc : checkG34 lc ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ := checkG34_spec hl hc
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ := checkG34_spec hl hc
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

/-! ## `v11`: `MOVB R1, R2` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 1 ∧ x = .int .w8 0xbe) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 3 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show BitVec.setWidth 8 (m0.x 1) = 0xbe
      decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g34Inv0 (h1 : (kAt lc kt 1 blk 3).get 1 = some 8) :
    G3Inv E lc (kAt lc kt 1 blk 3) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h1] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- `m0` keeps G34's table before `v11`: `X1` is zero-extended from 8 bits. -/
theorem uokl0 : UOKL m0 [(1, 8, false)] := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  show ∀ k : Nat, k < 31 → objX? 1 = some (BitVec.ofNat 5 k) →
    ExtOK (m0.x (BitVec.ofNat 5 k)) 8 false
  unfold ExtOK
  decide

/-- The per-value premises of `v11`, `MOVBreg`: none apply. -/
theorem pre11 {s : LocState} (hop : (val 11).op = .ARM64MOVBreg) : G14Pre lc s (val 11) := by
  have hne : ∀ o : Op, o ≠ .ARM64MOVBreg → (val 11).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G34 on `test/atomicload`'s `f`**: before `v11` (`MOVB R1, R2`, `a := int64(int8(x))`) G34's
table is `[(1, 8, false)]`. From the state with the byte `x = 0xbe` in `R1`, on a machine whose `X1`
is zero-extended from 8 bits, `g34_value` runs `v11`: `runLoc`'s `R2` holds the 64-bit sign
extension `0xffffffffffffffbe` and `R1` still the byte `0xbe`, and the machine state, related to it
before `v13` under an activation extending `E` that is again a `G28Env`, has
`X2 = 0xffffffffffffffbe`. G31's table is empty before `v13` (so `checkG33` rejects `f`), while
G34's still holds `R1`'s entry, which gives the whole `X1 = 0xbe`. -/
theorem genG34_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 11) = .ok s1 ∧
      s1.regs[2]? = some (.int .w64 0xffffffffffffffbe) ∧ s1.regs[1]? = some (.int .w8 0xbe) ∧
      uL31 lc (uIn lc 1) blk 4 = [] ∧ uL34 lc (uIn34 lc 1) blk 4 = [(1, 8, false)] ∧
      E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E1 s1 1 4 m1 ∧ UOKL m1 (uL34 lc (uIn34 lc 1) blk 4) ∧
      m1.x 2 = 0xffffffffffffffbe ∧ m1.x 1 = 0xbe := by
  obtain ⟨hl, hc, -, hav, hsl, hm1, hb, hv11, hi3, -, hop, -, -, -, hk1, -, hu3, hu31, hu4, hrun⟩ :=
    facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hr
  have hr2 := isW64_spec hr.1
  have hr1 := isW8_spec hr.2
  have hE := g34Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64MOVBreg → (val 11).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, hu1'⟩ := g34_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm1 hb hi3 hv11 (by rw [hop]; rfl) locMatch0 (g34Inv0 hk1) (by rw [hu3]; exact uokl0)
    (pre11 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  have hx2 : m1.x 2 = 0xffffffffffffffbe := valRel_i64 hA ((hm1'.regs 2 _ hr2).1 2 rfl)
  have hext : ExtOK (m1.x 1) 8 false := by
    have h := hu1'
    rw [hu4] at h
    exact h (1, 8, false) (by simp) 1 (by decide) rfl
  have hlo : (m1.x 1).setWidth 8 = 0xbe := (hm1'.regs 1 _ hr1).1 1 rfl
  have hx1' : m1.x 1 = 0xbe := by
    simp only [ExtOK, Bool.false_eq_true, ↓reduceIte] at hext
    rw [hext, hlo]
    decide
  exact ⟨s1, E1, m1, hs1, hr2, hr1, hu31, hu4, hx1, hE1, hp1, hm1', hu1', hx2, hx1'⟩

end GoFV.Proof.Witness.GenG34
