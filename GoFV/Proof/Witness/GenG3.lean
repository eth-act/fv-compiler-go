import GoFV.Proof.Gen.G3
import GoFV.Proof.Witness.GenG2

/-!
# Non-vacuity witness: slice G3 of the genssa validator on `pallocSum.start`

`std/runtime/pallocSum.start,1.ssa` and `std/runtime/pallocSum.start,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`startSsa`, `startProg`):

```go
func (p pallocSum) start() uint {
	if uint64(p)&uint64(1<<63) != 0 {
		return maxPackedValue
	}
	return uint(uint64(p) & (maxPackedValue - 1))
}
```

`checkG2` rejects it (the bit test `TBNZ`, `ANDconst`); `checkG3` accepts it with the PC table
`tab` and the class table `kt` (`R0` 64-bit at `b2` and `b3`). `GenG2.load` builds `checkG3`'s
input as `gen-check` does. By compiled evaluation (`native_decide`, listed in
`scripts/axioms-allowlist.txt`; `g3_facts`), from the state after `b1`'s entry values (`x` in
`R0`), `stepTermLoc` of `b1` (`TBNZ [63] v6`, emitted `TBZ $63, R0` to `b2`) goes to `b2` for
`x = 7` and to `b3` for `x = 2^63`, and in `b2` `stepLoc` runs `v19 = ANDconst [2097151] v6`
(`AND $2097151, R0, R0`). On a frameless activation with `G2Env` (`SP = 0x7fff0000`, every
symbol at `2^40`, `ι` the nil block and the globals there, the Progs at `0x10000 + 4·ID`,
`ret = 0`), `g3_term` gives a machine run to a state related before the first value of the
successor with the registers at its classes, and at `b2` `g3_value` continues the run past `v19`
(`genG3_witness_clear`, `genG3_witness_set`).
-/

namespace GoFV.Proof.Witness.GenG3

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/runtime/pallocSum.start,1.ssa` (quick-v10). -/
def startSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "pallocSum.start" 1 0 0
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
type t2 UINT64 8 8 0 comparable,named "pallocSum" "runtime.pallocSum"
type t3 UINT 8 8 0 comparable,named "uint" "uint"
type t1 FUNC 8 8 8 hasptr,direct "method(pallocSum) func() uint" "method(runtime.pallocSum) func() uint" 1 0 1
field 0 "p" t2 ? 0
field 1 "" t3 ? 0
aux a2 sym "runtime.pallocSum.start" "runtime.pallocSum.start" 1 - 0 - - - - 0
posbase p55 "runtime/mpagealloc.go" 1 1 -1
aux a3 name "p" "p" PPARAM t2 0 1 used p55:1049:7:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t3 0 1 - p55:1049:28:0:0
aux a1 call "AuxCall{runtime.pallocSum.start}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
type t4 BOOL 1 1 0 comparable,named "bool" "bool"
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
type t16 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t17 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t18 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t9
type t19 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t7
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t11
type t21 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t13
type t22 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t16
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
type t34 PTR 8 8 8 hasptr,direct,comparable "*pallocSum" "*runtime.pallocSum" t2
type t35 PTR 8 8 8 hasptr,direct,comparable "*uint" "*uint" t3
type t36 RESULTS ? ? ? - "uint,mem" "" 2 t3,t29
slot s1 a3 t2 0 - 0
f b1 t1 a1 22 3
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t8,UInt8=t9,UInt16=t10,UInt32=t11,UInt64=t12,Int=t13,Float32=t14,Float64=t15,UInt=t3,Uintptr=t16,String=t17,BytePtr=t18,Int32Ptr=t19,UInt32Ptr=t20,IntPtr=t21,UintptrPtr=t22,Float32Ptr=t23,Float64Ptr=t24,BytePtrPtr=t25,Complex64=t26,Complex128=t27,UnsafePtr=t28,Mem=t29,Flags=t30,Void=t31,Int128=t32,ResultMem=t33
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t35 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v7 Const64 t3 0 - p0:0:0:0:0 0 -
v v8 Copy t12 0 - p55:1050:12:2:0 1 v6
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:0:0 1 v8,v9
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v16 Copy t2 0 - p55:1053:21:2:0 1 v6
v v17 Copy t12 0 - p55:1053:21:2:0 1 v16
v v19 And64 t12 0 - p55:1053:24:0:0 1 v17,v18
v v20 Copy t3 0 - p55:1053:24:2:0 1 v19
v v21 Copy t29 0 - p55:1053:2:2:0 1 v1
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v20,v21
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v14 Copy t29 0 - p55:1051:3:2:0 1 v1
v v15 MakeResult t36 0 - p55:1051:3:0:0 1 v13,v14
names s1
named s1 v6,v16
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v7,v11,2097151=v18,2097152=v13
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t35 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v7 Const64 t3 0 - p0:0:0:0:0 0 -
v v8 Copy t12 0 - p55:1050:12:2:0 1 v6
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v8,v9
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v16 Copy t2 0 - p55:1053:21:2:0 1 v6
v v17 Copy t12 0 - p55:1053:21:2:0 1 v16
v v19 And64 t12 0 - p55:1053:24:1:0 1 v17,v18
v v20 Copy t3 0 - p55:1053:24:2:0 1 v19
v v21 Copy t29 0 - p55:1053:2:2:0 1 v1
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v20,v21
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v14 Copy t29 0 - p55:1051:3:2:0 1 v1
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v14
names s1
named s1 v6,v16
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v7,v11,2097151=v18,2097152=v13
freev -
freeb -
cache postorder b3,b2,b1
cache linestarts 55:1050:1053
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 6 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t35 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p55:1049:6:2:0 5 -
v v7 Const64 t3 0 - p0:0:0:0:0 0 -
v v8 Copy t12 0 - p55:1050:12:2:0 0 v6
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v6,v9
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v16 Copy t2 0 - p55:1053:21:2:0 0 v6
v v17 Copy t12 0 - p55:1053:21:2:0 0 v6
v v19 And64 t12 0 - p55:1053:24:1:0 2 v6,v18
v v20 Copy t3 0 - p55:1053:24:2:0 0 v19
v v21 Copy t29 0 - p55:1053:2:2:0 0 v1
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v14 Copy t29 0 - p55:1051:3:2:0 0 v1
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6,v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v7,v11,2097151=v18,2097152=v13
freev -
freeb -
cache postorder b3,b2,b1
cache linestarts 55:1050:1053
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v6,v9
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v6,v18
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 55:1050:1053
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v6,v9
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v6,v18
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 55:1050:1053
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v6,v9
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v6,v18
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 55:1050:1053
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v6,v9
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v6,v18
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 55:1050:1053
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v6,v9
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v6,v18
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 55:1050:1053
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v6,v9
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v6,v18
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 55:1050:1053
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v6,v9
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v6,v18
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 55:1050:1053
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p55:1049:6:2:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v14,v21,v20,v17,v16,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "p+0" a3 0
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v14 SB t16 0 - p0:0:0:0:0 0 -
v v21 SP t16 0 - p0:0:0:0:0 3 -
v v20 OffPtr t34 0 - p0:0:0:0:0 0 v21
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
v v17 LocalAddr t35 0 a4 p55:1053:2:0:0 0 v21,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
v v16 LocalAddr t35 0 a4 p55:1051:3:1:0 0 v21,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,v20,2097151=v18,2097152=v13
freev v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v14 SB t16 0 - p0:0:0:0:0 0 -
v v21 SP t16 0 - p0:0:0:0:0 3 -
v v20 OffPtr t34 0 - p0:0:0:0:0 0 v21
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
v v17 LocalAddr t35 0 a4 p55:1053:2:0:0 0 v21,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
v v16 LocalAddr t35 0 a4 p55:1051:3:1:0 0 v21,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,v20,2097151=v18,2097152=v13
freev v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v14 SB t16 0 - p0:0:0:0:0 0 -
v v21 SP t16 0 - p0:0:0:0:0 3 -
v v20 OffPtr t34 0 - p0:0:0:0:0 0 v21
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
v v17 LocalAddr t35 0 a4 p55:1053:2:0:0 0 v21,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
v v16 LocalAddr t35 0 a4 p55:1051:3:1:0 0 v21,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,v20,2097151=v18,2097152=v13
freev v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
v v14 SB t16 0 - p0:0:0:0:0 0 -
v v21 SP t16 0 - p0:0:0:0:0 3 -
v v20 OffPtr t34 0 - p0:0:0:0:0 0 v21
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
v v17 LocalAddr t35 0 a4 p55:1053:2:0:0 0 v21,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
v v16 LocalAddr t35 0 a4 p55:1051:3:1:0 0 v21,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,v20,2097151=v18,2097152=v13
freev v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v16,v17,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v16,v17,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v16,v17,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v16,v17,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v16,v17,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v16,v17,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v16,v17,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v16,v17,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 22 3
b b1 If p55:1050:32:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v9 Const64 t12 -9223372036854775808 - p0:0:0:0:0 1 -
v v11 Const64 t12 0 - p0:0:0:0:0 1 -
v v13 Const64 t3 2097152 - p0:0:0:0:0 1 -
v v18 Const64 t12 2097151 - p0:0:0:0:0 1 -
v v10 And64 t12 0 - p55:1050:14:1:0 1 v9,v6
v v12 Neq64 t4 0 - p55:1050:29:0:0 1 v10,v11
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 And64 t12 0 - p55:1053:24:1:0 1 v18,v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v9,0=v11,2097151=v18,2097152=v13
freev v16,v17,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 55:1050:1053
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v13 ARM64MOVDconst t3 2097152 - p0:0:0:0:0 1 -
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v13,v1
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v16,v12,v10,v18,v11,v9,v20,v21,v14,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.pallocSum.start}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v17 ARM64MOVDconst t3 2097152 - p55:1051:3:2:0 1 -
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v17,v1
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v8,v9,v10,v11,v12,v14,v16,v18,v20,v21
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
fstate scheduled,laidout
regalloc 23 v6:R0,v15:[],v17:R0,v19:R0,v22:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v17 ARM64MOVDconst t3 2097152 - p55:1051:3:2:0 1 -
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v17,v1
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v8,v9,v10,v11,v12,v14,v16,v18,v20,v21
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
fstate scheduled,laidout
regalloc 23 v6:R0,v15:[],v17:R0,v19:R0,v22:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 22 3
b b1 ARM64TBNZ p55:1050:32:1:0 0 63 - v6 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p55:1050:32:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
b b3 Ret p55:1051:10:1:0 0 0 - v15 - b1:0
v v17 ARM64MOVDconst t3 2097152 - p55:1051:3:2:0 1 -
v v15 MakeResult t36 0 - p55:1051:3:1:0 1 v17,v1
b b2 Ret p55:1053:42:1:0 0 0 - v22 - b1:1
v v19 ARM64ANDconst t12 2097151 - p55:1053:24:1:0 1 v6
v v22 MakeResult t36 0 - p55:1053:2:0:0 1 v19,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v8,v9,v10,v11,v12,v14,v16,v18,v20,v21
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 55:1050:1053
fstate scheduled,laidout
regalloc 23 v6:R0,v15:[],v17:R0,v19:R0,v22:[]
dcllen 2
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t22,t25,t26,t27,t28
typelink t29=t33
typeorder t5,t9,t6,t10,t7,t11,t8,t12,t2,t13,t3,t16,t26,t27,t14,t15,t4,t18,t19,t20,t34,t21,t35,t22,t23,t24,t25,t1,t17,t28,t29,t31,t30,t32,t33,t36
eof
"#

/-- `std/runtime/pallocSum.start,1.prog` (quick-v10). -/
def startProg : String := r#"gofv-prog 3
pkg "runtime"
func "pallocSum.start" 1
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
type t1 8 8 0 0 - "pallocSum"
name n1 "p" PPARAM t1 1 "runtime.p" 0 a3
type t2 8 8 0 0 - "uint"
name n2 "~r0" PPARAMOUT t2 1 "runtime.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p55 "runtime/mpagealloc.go" 1 1 -1 54 "runtime/mpagealloc.go" "runtime/mpagealloc.go" 1 1
sym y1 "runtime.pallocSum.start" 1
curfn p55:1049:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 1049 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.pallocSum.start.arginfo1" 0
sym y4 "runtime.pallocSum.start.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p55:1049:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p55:1049:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p55:1049:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p55:1049:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p55:1049:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p55:1049:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p55:1050:32:1:0
p 7 7 0 0 0 - TBZ 0 CONST/0/0/0/NONE/0/63/-/- 8192 - BRANCH/0/0/0/NONE/0/0/-/@10 0 0 p55:1050:32:1:0
p 8 8 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/2097152/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p55:1051:3:1:0
p 9 9 0 0 0 - RET 0 _ 0 - _ 0 0 p55:1051:10:2:0
p 10 10 0 0 0 - AND 0 CONST/0/0/0/NONE/0/2097151/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p55:1053:24:1:0
p 11 11 0 0 0 - RET 0 _ 0 - _ 0 0 p55:1053:42:2:0
p 12 12 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 1049 201080
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
dbgloc 0 1:-10000:3:17:50
dbgregout n2
dbgpc 3:17:9
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p55:1049:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p55:1049:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p55:1049:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p55:1049:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p55:1049:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p55:1049:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p55:1050:32:1:0
p 7 0 0 0 470 - TBZ 0 CONST/0/0/0/NONE/17/63/-/- 8192 - BRANCH/0/0/0/NONE/36/10/-/@10 0 0 p55:1050:32:1:0
p 8 4 0 0 319 - MOVD 0 CONST/0/0/0/NONE/19/2097152/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p55:1051:3:1:0
p 9 8 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p55:1051:10:2:0
p 10 12 0 0 57 - AND 0 CONST/0/0/0/NONE/24/2097151/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p55:1053:24:1:0
p 11 16 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p55:1053:42:2:0
fn y1 8 0 0 0 1049 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 32 0 6000f8b6e0036bb2c0035fd600504092c0035fd6000000000000000000000000 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 54
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 3 1 28000 010800 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040800 0
data y9 SRODATA 3 1 28000 020800 0
data y10 SRODATA 3 1 28000 6e0800 0
data y11 SRODATA 8 1 28000 b610010202040500 0
data y12 SRODATA 3 1 28000 000800 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "go:info.runtime.pallocSum.start$abstract" 0
sym y17 "" 0
sym y18 "go:info.runtime.pallocSum" 0
sym y19 "go:info.uint" 0
sym y20 "type:uint" 0
dwfn y13 y14 y15 y16 y17 "runtime.pallocSum.start" 54:1049 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y16 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "runtime.pallocSum" 0 0 1 p55:1049:7:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uint" 0 0 1 p55:1049:28:0:0
var 0 0 "p" 5 1 0 0 0 8 y18 "runtime/mpagealloc.go" 1049 7 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y19 "runtime/mpagealloc.go" 1049 28 0 1 0 0 -
scope 0 0 - 0,1
dieref y13 3 y16 0
dieoff y16 0:29
data y13 SDWARFFCN 33 0 0 0600000000000020019c2900000000000000002e7e723000019908000000000000 6
reloc 0 0 R_USETYPE 0 y20
reloc 1 4 R_DWARFSECREF 0 y16
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y16
reloc 15 4 R_DWARFSECREF 0 y14
reloc 27 4 R_DWARFSECREF 0 y19
data y14 SDWARFLOC 9 0 0 010000040008015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 29 0 0 0009020000000000000000043703940814380637063906370210000101 1
reloc 3 8 R_ADDR 0 y1
data y16 SDWARFABSFCN 38 0 1 0572756e74696d652e70616c6c6f6353756d2e73746172740001990801227000000000000000 1
reloc 33 4 R_DWARFSECREF 0 y18
end
eof
"#

/-- The loaded `pallocSum.start` (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load startSsa startProg

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

/-- The PC table `checkG3` gives: per block, the index of each value's first Prog and of the
terminator's. -/
def tab : PcTab := [(1, [5, 5, 5]), (3, [8, 9, 9]), (2, [10, 11, 11])]

/-- `R0` holds a 64-bit value, nothing else is known. -/
def kR0 : KMap := KMap.bot.set! 0 (some 64)

/-- The class table `checkG3` gives: nothing known at the entry `b1`; `R0` 64-bit at `b2`, `b3`. -/
def kt : KTab := [(1, KMap.bot), (3, kR0), (2, kR0)]

/-- Block `b1`: the entry values `v6 = ArgIntReg` (`R0`) and `v1 = InitMem`; `TBNZ [63] v6` to
`b3`, `b2`. -/
def blk1 : Block := (lc.ctx.f.block? 1).getD default

/-- Block `b2`: `v19 = ANDconst [2097151] v6` (`R0`), `v22 = MakeResult v19 v1`; `Ret`. -/
def blk2 : Block := (lc.ctx.f.block? 2).getD default

def v19 : Value := (lc.ctx.f.value? 19).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, no frame, every symbol at `symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 0 0 ps.toList

/-- A frameless activation (`SP = 0x7fff0000`, `g = 0x9000`, `LR = 0x40`, `FP = 0`) with the
globals at their symbols and the PC table of `checkG3`. -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := 0x7fff0000, slot := fun _ => none, g := 0x9000, lr := 0x40, fp := 0,
    framed := false, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The machine at `b1`'s terminator: `X0 = x`, the activation's `g`, `FP`, `LR`. -/
def m0 (x : BitVec 64) : MState :=
  { x := fun k => if k = 0 then x else if k = 28 then 0x9000 else if k = 29 then 0 else
      if k = 30 then 0x40 else 0,
    sp := 0x7fff0000, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 blk1.values.size, mem := fun _ => 0 }

/-- What compiled evaluation checks: `checkG3` accepts `pallocSum.start` and `checkG2` does not;
there is no home slot and no static call; `b1` (two values) and `b2` are laid out, `b2` starts
with `v19 = ANDconst`; `R0` holds a 64-bit value at the end of `b1`; from the state after the
entry values (`x` in `R0`), `b1`'s terminator goes to block `t`, and in `b2` `stepLoc` runs
`v19`. -/
def startFacts (x : BitVec 64) (t : ID) : Bool :=
  (checkG3 lc ps bs g).toOption == some (tab, kt) && (checkG2 lc ps bs g).toOption.isNone &&
    (homeSlots lc).isEmpty &&
    GenG2.noCalls lc && lc.ctx.f.blocks.toList.contains 1 && lc.ctx.f.blocks.toList.contains 2 &&
    (lc.ctx.f.block? 1).isSome && (lc.ctx.f.block? 2).isSome && (lc.ctx.f.value? 19).isSome &&
    blk1.values.size == 2 && blk1.kind == .ARM64TBNZ && blk2.values[0]? == some 19 &&
    v19.op == .ARM64ANDconst && (kAt lc kt 1 blk1 2).get 0 == some 64 &&
    GenG1.okThen (stepTermLoc lc (GenG2.s0 x) blk1) fun r => GenG1.gotoIs r.1 t &&
      (t != 2 || GenG1.okThen (stepLoc default lc r.2 v19) fun _ => true)

/-- From `x = 7` (bit 63 clear) to `b2`, from `x = 2^63` (bit 63 set) to `b3`. -/
theorem g3_facts : (startFacts 7 2 && startFacts 0x8000000000000000 3) = true := by
  native_decide

theorem g3Env (hc : checkG3 lc ps bs g = .ok (tab, kt)) (hsl : (homeSlots lc).isEmpty = true)
    (hnc : GenG2.noCalls lc = true) : G2Env lc g L ps 0 tab E where
  lcEq := rfl
  link := rfl
  pcOf := rfl
  retOut := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG3_spec hc
    intro p hp
    exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
  addr := GenG2.addrAgree
  glob := fun _ _ _ _ => rfl
  syms := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG3_spec hc
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
  frame := ⟨by decide, by decide, fun k off h => by cases h⟩

theorem locMatch0 (x : BitVec 64) : LocMatch E (GenG2.s0 x) 1 blk1.values.size (m0 x) where
  regs := by
    intro r v hv
    simp only [GenG2.s0, Array.getElem?_ofFn] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · split at hv
        · subst hv
          rename_i h0
          subst h0
          simp only [objX?] at hk
          cases hk
          exact Or.inl rfl
        · subst hv; trivial
      · split at hv
        · rename_i h0; subst h0; simp [objV?] at hk
        · subst hv; trivial
    · cases hv
  flags := trivial
  slots := by intro k v h; simp [GenG2.s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, (fun h => by cases h), fun _ => ⟨rfl, rfl⟩⟩
  pc := rfl

theorem g3Inv0 (x : BitVec 64) {K : KMap} (h0 : K.get 0 = some 64) :
    G3Inv E lc K (GenG2.s0 x) where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, GenG2.keys0, GenG2.sep0⟩
    simp only [GenG2.s0, Array.getElem?_ofFn] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      split at hv
      · rename_i h0'
        subst hv; subst h0'
        rw [h0] at hc; cases hc; rfl
      · subst hv; trivial
    · cases hv
  slots := by intro k v h; simp [GenG2.s0] at h

/-- **G3 on `pallocSum.start`**: from the state after the entry values of `b1` (`x` in `R0`),
`g3_term` on the bit test `TBNZ [63]` (emitted `TBZ $63, R0`) gives a machine run of the Progs to
a state related before the first value of the block `runLoc` goes to, with the registers at that
block's classes; at `b2` (bit 63 clear), `g3_value` on `v19 = ANDconst` (`AND $2097151, R0, R0`)
continues the run to a state related before `v22`. -/
theorem genG3_witness (x : BitVec 64) (t : ID) (hf : startFacts x t = true) :
    ∃ s1 e m1, stepTermLoc lc (GenG2.s0 x) blk1 = .ok (.goto e, s1) ∧ e.b = t ∧
      PStar GenG2.H0 L ps.toList 0 (m0 x) m1 ∧ LocMatch E s1 t 0 m1 ∧
      G3Inv E lc (kt.at t) s1 ∧
      (t = 2 → ∃ s2 E' m2, stepLoc default lc s1 v19 = .ok s2 ∧ E.Extends E' ∧
        PStar GenG2.H0 L ps.toList 0 m1 m2 ∧ LocMatch E' s2 2 1 m2 ∧
        G3Inv E' lc (kAt lc kt 2 blk2 1) s2) := by
  simp only [startFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hsl⟩, hnc⟩, hm1⟩, hm2⟩, hb1s⟩, hb2s⟩, hv19s⟩, hsz⟩, hkind⟩,
    h2⟩, hop⟩, hk0⟩, hrun⟩ := hf
  have hc : checkG3 lc ps bs g = .ok (tab, kt) := by
    revert hres; cases checkG3 lc ps bs g <;> simp [Except.toOption]
  have hb1 : lc.ctx.f.block? 1 = some blk1 := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [blk1, hb]
  have hb2 : lc.ctx.f.block? 2 = some blk2 := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb2s
    simp [blk2, hb]
  have hv : lc.ctx.f.value? 19 = some v19 := by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv19s
    simp [v19, hv]
  have hE := g3Env hc hsl hnc
  obtain ⟨⟨n, s1⟩, hs1, hrun⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨hgo, hrun⟩ := hrun
  obtain ⟨e, rfl, het⟩ := GenG1.gotoIs_spec hgo
  obtain ⟨m1, hp1, hlm1, hinv1, -⟩ := g3_term (H := GenG2.H0) hc hE hm1 hb1 (locMatch0 x)
    (g3Inv0 x (by rw [hsz]; exact hk0))
    (fun hz => by rw [hkind] at hz; rcases hz with h | h <;> cases h) hs1
  refine ⟨s1, e, m1, hs1, het, hp1, het ▸ hlm1, het ▸ hinv1, fun ht2 => ?_⟩
  subst ht2
  obtain ⟨s2, hs2, -⟩ := GenG1.okThen_spec (by simpa using hrun)
  have hen : entryOp3 v19.op = false := by rw [hop]; rfl
  have hpre : G3Pre lc s1 v19 := by
    refine ⟨fun h => ?_, fun as n sg hl => ?_, fun h => by rw [hop] at h; cases h⟩
    · rcases h with h | h <;> rw [hop] at h <;> cases h
    · rw [hop] at hl; simp [loadOp?, narrowLoad?] at hl
  have hinv1' : G3Inv E lc (kAt lc kt 2 blk2 0) s1 := by rw [kAt_zero, ← het]; exact hinv1
  obtain ⟨E', m2, hx, -, hp2, hlm2, hinv2⟩ := g3_value (H := GenG2.H0) (env := default) hc hE hm2
    hb2 h2 hv hen (het ▸ hlm1) hinv1' hpre (GenG2.callOK_ne (by rw [hop]; nofun)) hs2
  exact ⟨s2, E', m2, hs2, hx, hp2, hlm2, hinv2⟩

/-- Bit 63 of `x = 7` is clear: `b2`, then `v19`. -/
theorem genG3_witness_clear :
    ∃ s1 e m1 s2 E' m2, stepTermLoc lc (GenG2.s0 7) blk1 = .ok (.goto e, s1) ∧ e.b = 2 ∧
      PStar GenG2.H0 L ps.toList 0 (m0 7) m1 ∧ LocMatch E s1 2 0 m1 ∧
      G3Inv E lc (kt.at 2) s1 ∧ stepLoc default lc s1 v19 = .ok s2 ∧ E.Extends E' ∧
      PStar GenG2.H0 L ps.toList 0 m1 m2 ∧ LocMatch E' s2 2 1 m2 ∧
      G3Inv E' lc (kAt lc kt 2 blk2 1) s2 := by
  have h := g3_facts
  simp only [Bool.and_eq_true] at h
  obtain ⟨s1, e, m1, h1, h2, h3, h4, h5, h6⟩ := genG3_witness 7 2 h.1
  obtain ⟨s2, E', m2, h7, h8, h9, h10, h11⟩ := h6 rfl
  exact ⟨s1, e, m1, s2, E', m2, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11⟩

/-- Bit 63 of `x = 2^63` is set: `b3`. -/
theorem genG3_witness_set :
    ∃ s1 e m1, stepTermLoc lc (GenG2.s0 0x8000000000000000) blk1 = .ok (.goto e, s1) ∧ e.b = 3 ∧
      PStar GenG2.H0 L ps.toList 0 (m0 0x8000000000000000) m1 ∧ LocMatch E s1 3 0 m1 ∧
      G3Inv E lc (kt.at 3) s1 := by
  have h := g3_facts
  simp only [Bool.and_eq_true] at h
  obtain ⟨s1, e, m1, h1, h2, h3, h4, h5, -⟩ := genG3_witness _ 3 h.2
  exact ⟨s1, e, m1, h1, h2, h3, h4, h5⟩

end GoFV.Proof.Witness.GenG3
