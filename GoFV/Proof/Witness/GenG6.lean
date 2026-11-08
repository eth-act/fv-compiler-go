import GoFV.Proof.Gen.G6
import GoFV.Proof.Witness.GenG5

/-!
# Non-vacuity witness: slice G6 of the genssa validator on `SChan.Send` of `test/closedchan`

`test/closedchan/main/SChan.Send,1.ssa` and `test/closedchan/main/SChan.Send,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`sendSsa`, `sendProg`):

```go
func (c SChan) Send(x int) {
	c <- x
}
```

`checkG5` rejects it (the frame variable `.autotmp_3`, a `PAUTO` whose address is never converted
to an integer: `v9 = MOVDstore {.autotmp_3} v2 v7 v1`); `checkG6` accepts it with the PC table
`tab` and the class table `kt` (nothing known at the entry). By compiled evaluation
(`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g6_facts`), from the state after the
entry values (`x = 7` in `R1`; the memory holds `.autotmp_3`'s block `Blk.temp 0 5` of 8 poison
bytes), `stepLoc` runs the store `v9` of `x` to `.autotmp_3` and the address `v10 = MOVDaddr
{.autotmp_3} v2`. On GenG2's framed layout (`SP = 0x7fff0000`, `autosize = 32`, `extrasize = 8`,
every symbol at `2^40`, the Progs at `0x10000 + 4·ID`, `ret = 0`) with `.autotmp_3` (operand
`-8`, `NAME_AUTO`) at `SP + 16` under the injection (`G6Env`), `g6_value` twice gives a machine run
of the Progs (`MOVD R1, -8(RSP)`; `MOVD $-8(RSP), R1`) to a state related before the call `v12`,
with the registers at their classes (`genG6_value_witness`). `checkG6` also accepts
`pallocSum.start` (`GenG3`, no frame variable) with G3's tables; there `g6_term` runs the bit test
`TBNZ [63]` to `b2` (`genG6_term_witness`).
-/

namespace GoFV.Proof.Witness.GenG6

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/closedchan/main/SChan.Send,1.ssa` (quick-v10). -/
def sendSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "SChan.Send" 1 0 0
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
type t2 CHAN 8 8 8 hasptr,direct,comparable,named "SChan" "main.SChan"
type t3 INT 8 8 0 comparable,named "int" "int"
type t1 FUNC 8 8 8 hasptr,direct "method(SChan) func(int)" "method(main.SChan) func(int)" 1 1 0
field 0 "c" t2 ? 0
field 1 "x" t3 ? 0
aux a2 sym "main.SChan.Send" "main.SChan.Send" 1 - 0 - - - - 0
posbase p2 "./closedchan.go" 1 1 -1
aux a3 name "c" "c" PPARAM t2 0 1 used p2:86:7:0:0
aux a4 name "x" "x" PPARAM t3 8 1 used p2:86:21:0:0
aux a1 call "AuxCall{main.SChan.Send}" a2 1 2 0 8 16 2 0
abiparam in 0 t2 a3 0 0
abiparam in 1 t3 a4 1 8
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
type t34 PTR 8 8 8 hasptr,direct,comparable "*SChan" "*main.SChan" t2
aux a5 name ".autotmp_3" ".autotmp_3" PAUTO t3 0 3 addrtaken,used,autotmp p2:88:2:0:0
aux a6 type "int" t3
type t35 CHAN 8 8 8 hasptr,direct,comparable "chan<- int" "chan<- int"
aux a8 sym "runtime.chansend1" "runtime.chansend1" 1 - 0 - - - - 0
aux a7 call "AuxCall{runtime.chansend1}" a8 1 2 0 8 16 2 0
abiparam in 0 t35 - 0 0
abiparam in 1 t21 - 1 8
slot s1 a3 t2 0 - 0
slot s2 a4 t3 0 - 0
f b1 t1 a1 15 2
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t8,UInt8=t9,UInt16=t10,UInt32=t11,UInt64=t12,Int=t3,Float32=t13,Float64=t14,UInt=t15,Uintptr=t16,String=t17,BytePtr=t18,Int32Ptr=t19,UInt32Ptr=t20,IntPtr=t21,UintptrPtr=t22,Float32Ptr=t23,Float64Ptr=t24,BytePtrPtr=t25,Complex64=t26,Complex128=t27,UnsafePtr=t28,Mem=t29,Flags=t30,Void=t31,Int128=t32,ResultMem=t33
b b1 Plain p2:88:2:1:0 0 0 - - b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v2 SP t16 0 - p0:0:0:0:0 4 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 1 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 2 v8,v7,v1
v v10 Copy t35 0 - p2:88:9:2:0 1 v6
v v11 LocalAddr t21 0 a5 p2:88:9:2:0 1 v2,v9
v v12 StaticLECall t33 16 a7 p2:88:9:0:0 1 v10,v11,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
b b2 Ret p2:90:1:0:0 0 0 - v15 - b1:0
v v14 Copy t29 0 - p2:90:1:2:0 1 v13
v v15 MakeResult t33 0 - p2:90:1:0:0 1 v14
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev -
freeb -
dcllen 4
end
pass 1 "number lines"
f b1 t1 a1 15 2
b b1 Plain p2:88:2:1:0 0 0 - - b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v2 SP t16 0 - p0:0:0:0:0 4 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 1 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 2 v8,v7,v1
v v10 Copy t35 0 - p2:88:9:2:0 1 v6
v v11 LocalAddr t21 0 a5 p2:88:9:2:0 1 v2,v9
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v10,v11,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
b b2 Ret p2:90:1:0:0 0 0 - v15 - b1:0
v v14 Copy t29 0 - p2:90:1:2:0 1 v13
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v14
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev -
freeb -
cache postorder b2,b1
cache linestarts 2:88:90
dcllen 4
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 15 2
b b1 Plain p2:88:2:1:0 0 0 - - b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 4 -
v v2 SP t16 0 - p0:0:0:0:0 4 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:86:6:2:0 2 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 1 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 2 v8,v7,v1
v v10 Copy t35 0 - p2:88:9:2:0 0 v6
v v11 LocalAddr t21 0 a5 p2:88:9:2:0 1 v2,v9
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v11,v9
v v13 SelectN t29 0 - p2:88:9:0:0 2 v12
b b2 Ret p2:90:1:0:0 0 0 - v15 - b1:0
v v14 Copy t29 0 - p2:90:1:2:0 0 v13
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev -
freeb -
cache postorder b2,b1
cache linestarts 2:88:90
dcllen 4
end
pass 3 "early deadcode"
f b1 t1 a1 15 2
b b1 Plain p2:88:2:1:0 0 0 - - b2:0 -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 1 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 2 v8,v7,v1
v v11 LocalAddr t21 0 a5 p2:88:9:2:0 1 v2,v9
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v11,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
b b2 Ret p2:90:1:0:0 0 0 - v15 - b1:0
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v14,v10,v5,v4,v3
freeb -
cache postorder b2,b1
cache linestarts 2:88:90
dcllen 4
end
pass 4 "short circuit"
f b2 t1 a1 15 2
b b1 BlockInvalid p2:88:2:1:0 0 0 - - - -
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 1 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 2 v8,v7,v1
v v11 LocalAddr t21 0 a5 p2:88:9:2:0 1 v2,v9
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v11,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v14,v10,v5,v4,v3
freeb -
cache linestarts 2:88:90
dcllen 4
end
pass 5 "decompose user"
f b2 t1 a1 15 2
b b1 BlockInvalid p2:88:2:1:0 0 0 - - - -
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 1 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 2 v8,v7,v1
v v11 LocalAddr t21 0 a5 p2:88:9:2:0 1 v2,v9
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v11,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v14,v10,v5,v4,v3
freeb -
cache linestarts 2:88:90
dcllen 4
end
pass 6 "pre-opt deadcode"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 1 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 2 v8,v7,v1
v v11 LocalAddr t21 0 a5 p2:88:9:2:0 1 v2,v9
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v11,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v14,v10,v5,v4,v3
freeb b1
cache linestarts 2:88:90
dcllen 4
end
pass 7 "opt"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 1 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 2 v8,v7,v1
v v11 LocalAddr t21 0 a5 p2:88:9:2:0 1 v2,v9
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v11,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v14,v10,v5,v4,v3
freeb b1
cache linestarts 2:88:90
dcllen 4
end
pass 8 "zero arg cse"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 1 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 2 v8,v7,v1
v v11 LocalAddr t21 0 a5 p2:88:9:2:0 1 v2,v9
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v11,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v14,v10,v5,v4,v3
freeb b1
cache linestarts 2:88:90
dcllen 4
end
pass 9 "opt deadcode"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 1 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 2 v8,v7,v1
v v11 LocalAddr t21 0 a5 p2:88:9:2:0 1 v2,v9
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v11,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v14,v10,v5,v4,v3
freeb b1
cache linestarts 2:88:90
dcllen 4
end
pass 10 "generic cse"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 2 v8,v7,v1
v v11 LocalAddr t21 0 a5 p2:88:9:2:0 0 v2,v9
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v14,v10,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 11 "phiopt"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 2 v8,v7,v1
v v11 LocalAddr t21 0 a5 p2:88:9:2:0 0 v2,v9
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v14,v10,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 12 "gcse deadcode"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v11,v14,v10,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 13 "nilcheckelim"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v11,v14,v10,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 14 "prove"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v11,v14,v10,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 15 "divisible"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v11,v14,v10,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 16 "divmod"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v11,v14,v10,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 17 "middle opt"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v11,v14,v10,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 18 "known bits"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v11,v14,v10,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 19 "early fuse"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:86:6:2:0 1 -
v v7 Arg t3 0 a4 p2:86:6:2:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticLECall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v11,v14,v10,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 20 "expand calls"
aux a9 nameoff "c+0" a3 0
aux a10 nameoff "x+0" a4 0
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
v v11 SB t16 0 - p0:0:0:0:0 0 -
v v14 OffPtr t34 0 - p0:0:0:0:0 0 v2
v v10 OffPtr t21 0 - p0:0:0:0:0 0 v2
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts 0=v14,v10
freev v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 21 "decompose builtin"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
v v11 SB t16 0 - p0:0:0:0:0 0 -
v v14 OffPtr t34 0 - p0:0:0:0:0 0 v2
v v10 OffPtr t21 0 - p0:0:0:0:0 0 v2
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts 0=v14,v10
freev v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 22 "softfloat"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
v v11 SB t16 0 - p0:0:0:0:0 0 -
v v14 OffPtr t34 0 - p0:0:0:0:0 0 v2
v v10 OffPtr t21 0 - p0:0:0:0:0 0 v2
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts 0=v14,v10
freev v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 23 "branchelim"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
v v11 SB t16 0 - p0:0:0:0:0 0 -
v v14 OffPtr t34 0 - p0:0:0:0:0 0 v2
v v10 OffPtr t21 0 - p0:0:0:0:0 0 v2
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts 0=v14,v10
freev v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 24 "late opt"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 25 "dead auto elim"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 26 "sccp"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 27 "generic deadcode"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 28 "late fuse"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 29 "check bce"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 30 "dse"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 31 "memcombine"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 32 "writebarrier"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v2 SP t16 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 LocalAddr t21 0 a5 p2:88:2:2:0 2 v2,v1
v v9 Store t29 0 a6 p2:88:2:2:0 1 v8,v7,v1
v v12 StaticCall t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 33 "lower"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 34 "addressing modes"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 35 "late lower"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 36 "pair"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 37 "lowered deadcode for cse"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4
cache linestarts 2:88:90
dcllen 4
end
pass 38 "lowered cse"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
dcllen 4
end
pass 39 "elim unread autos"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
dcllen 4
end
pass 40 "tighten tuple selectors"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
dcllen 4
end
pass 41 "lowered deadcode"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
dcllen 4
end
pass 42 "checkLower"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
dcllen 4
end
pass 43 "loop invariant"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
dcllen 4
end
pass 44 "late phielim and copyelim"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
dcllen 4
end
pass 45 "tighten"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
dcllen 4
end
pass 46 "late deadcode"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
dcllen 4
end
pass 47 "critical"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
dcllen 4
end
pass 48 "phi tighten"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
dcllen 4
end
pass 49 "likelyadjust"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
dcllen 4
end
pass 50 "layout"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
fstate laidout
dcllen 4
end
pass 51 "schedule"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
fstate scheduled,laidout
dcllen 4
end
pass 52 "late nilcheck"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
fstate scheduled,laidout
dcllen 4
end
pass 53 "flagalloc"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v8 ARM64MOVDaddr t21 0 a5 p2:88:2:2:0 1 v2
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v8,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v10,v14,v11,v5,v4,v3
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
fstate scheduled,laidout
dcllen 4
end
pass 54 "regalloc"
aux a7 call "AuxCall{runtime.chansend1}" a8 1 2 0 8 16 2 0
abiparam in 0 t35 - 0 0
abiparam in 1 t21 - 1 8
callreg 0:1,1:2 - 7fffffff97ffffff -
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v10 ARM64MOVDaddr t21 0 a5 p2:88:9:2:0 1 v2
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v10,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v3,v4,v5,v11,v14
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
fstate scheduled,laidout
regalloc 13 v2:SP,v6:R0,v7:R1,v10:R1,v12:[]
dcllen 4
end
pass 55 "loop rotate"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v10 ARM64MOVDaddr t21 0 a5 p2:88:9:2:0 1 v2
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v10,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v3,v4,v5,v11,v14
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
fstate scheduled,laidout
regalloc 13 v2:SP,v6:R0,v7:R1,v10:R1,v12:[]
dcllen 4
end
pass 56 "trim"
f b2 t1 a1 15 2
b b2 Ret p2:90:1:0:0 0 0 - v15 - -
v v6 ArgIntReg t2 0 a9 p2:90:1:0:0 1 -
v v7 ArgIntReg t3 1 a10 p2:90:1:0:0 1 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDstore t29 0 a5 p2:88:2:2:0 1 v2,v7,v1
v v10 ARM64MOVDaddr t21 0 a5 p2:88:9:2:0 1 v2
v v12 ARM64CALLstatic t33 16 a7 p2:88:9:1:0 1 v6,v10,v9
v v13 SelectN t29 0 - p2:88:9:0:0 1 v12
v v15 MakeResult t33 0 - p2:90:1:1:0 1 v13
names s1,s2
named s1 v6
named s2 v7
splits -
canon a3/t2/0/-/0=s1,a4/t3/0/-/0=s2
consts -
freev v3,v4,v5,v11,v14
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a9:5,a10:6
cache linestarts 2:88:90
fstate scheduled,laidout
regalloc 13 v2:SP,v6:R0,v7:R1,v10:R1,v12:[]
dcllen 4
end
frontend
end
ptrcache t2,t3,t6,t7,t8,t9,t11,t13,t14,t16,t17,t18,t25
typelink t29=t33
typeorder t5,t9,t6,t10,t7,t11,t8,t12,t3,t15,t16,t26,t27,t13,t14,t4,t18,t19,t20,t21,t22,t23,t24,t25,t34,t1,t35,t2,t17,t28,t29,t31,t30,t32,t33
eof
"#

/-- `test/closedchan/main/SChan.Send,1.prog` (quick-v10). -/
def sendProg : String := r#"gofv-prog 3
pkg "main"
func "SChan.Send" 1
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
type t1 8 8 8 1 01 "SChan"
name n1 "c" PPARAM t1 1 "main.c" 0 a3
type t2 8 8 0 0 - "int"
name n2 "x" PPARAM t2 1 "main.x" 0 a4
name n3 ".autotmp_2" PAUTO t1 3 "main..autotmp_2" 0 -
name n4 ".autotmp_3" PAUTO t2 3 "main..autotmp_3" 0 a5
in n1 0 used
in n2 8 used
in n3 0 used,autotmp
in n4 0 used,addrtaken,autotmp
out n1 0 used
out n2 8 used
out n4 -8 used,addrtaken,autotmp
opt n3 0 autotmp
stack 8 0 8
end
genin
posbase p2 "./closedchan.go" 1 1 -1 1 "./closedchan.go" "./closedchan.go" 1 1
sym y1 "main.SChan.Send" 1
curfn p2:86:6:0:0 0 0
regargs 8192:0:t1,8193:8:t2
text y1 0 0 0 0 86 201080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "main.SChan.Send.arginfo1" 0
sym y5 "main.SChan.Send.argliveinfo" 0
sym y6 "main..autotmp_3" 0
sym y7 "runtime.chansend1" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i16 0 0 p2:86:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:86:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:86:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:86:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:86:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:86:6:2:0
p 6 6 0 0 0 - MOVD 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/AUTO/0/-8/y6/- 0 0 p2:88:9:1:0
p 7 7 0 0 0 - MOVD 0 ADDR/8383/0/0/AUTO/0/-8/y6/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:88:9:2:0
p 8 8 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:88:9:2:0
p 9 9 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p2:88:9:2:0
p 10 10 0 0 0 - RET 0 _ 0 - _ 0 0 p2:90:1:0:0
p 11 11 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 86 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 2
dbgslot 0 n1 t1 0
dbgslot 1 n2 t2 0
dbgvar 0 n1 0
dbgvar 1 n2 1
dbgloc 0 2:-10000:2:12:50
dbgloc 1 2:-10000:2:10:51
dbgregout -
dbgpc 2:12:10,2:10:8
end
asm
sym y8 "runtime.morestack_noctxt" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/48/-/i16 0 0 p2:86:6:0:0
p 12 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:86:6:0:0
p 13 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:86:6:0:0
p 14 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:86:6:0:0
p 15 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@24 0 0 p2:86:6:0:0
p 16 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:86:6:0:0
p 17 12 48 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-48/-/- 0 0 p2:86:6:0:1
p 18 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:86:6:0:0
p 19 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:86:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:86:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:86:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:86:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p2:86:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:86:6:2:0
p 6 24 0 0 304 - MOVD 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/AUTO/47/-8/y6/- 0 0 p2:88:9:1:0
p 7 28 0 0 325 - MOVD 0 ADDR/0/0/0/AUTO/32/-8/y6/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:88:9:2:0
p 8 32 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:88:9:2:0
p 9 32 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y7/- 0 0 p2:88:9:2:0
p 10 36 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:90:1:0:0
p 20 40 -48 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/48/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:90:1:0:0
p 21 44 48 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:90:1:0:0
p 22 48 -48 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:90:1:0:0
p 23 48 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:86:6:0:0
p 24 48 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:86:6:0:0
p 25 48 0 0 436 - STP 0 REGREG/8192/0/0/NONE/7/8193/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p2:86:6:0:0
p 26 52 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:86:6:0:0
p 27 56 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y8/- 0 0 p2:86:6:0:0
p 28 60 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:86:6:0:0
p 29 60 0 0 245 - LDP 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REGREG/8192/0/0/NONE/7/8193/-/- 0 0 p2:86:6:0:0
p 30 64 48 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@12 0 0 p2:86:6:0:0
fn y1 16 40 0 0 86 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
funcaux y2 y3 - - y4 y5 -
text 80 0 900b40f9ff6330eb49010054fe0f1df8fd831ff8fd2300d1e11300f9e183009100000094fd835ff8fe0743f8c0035fd6e08700a9e3031eaa00000094e08740a9f0ffff17000000000000000000000000 2
reloc 32 4 R_CALLARM64 0 y7
reloc 56 4 R_CALLARM64 0 y8
pcln y13 y14 y15 y16 y9,y10,y11,y12 y2,y3,_,_,_,y4,y5
usedfiles 1
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 5 1 8000 00080808ff 0
data y5 SDATA 2 1 8000 0000 0
data y9 SRODATA 11 1 28000 0001010202090103020500 0
data y10 SRODATA 7 1 28000 00080404030800 0
data y11 SRODATA 0 1 28000 - 0
data y12 SRODATA 5 1 28000 0006040e00 0
data y13 SRODATA 7 1 28000 020460075f0900 0
data y14 SRODATA 3 1 28000 041400 0
data y15 SRODATA 10 1 28000 ae010604030403070800 0
data y16 SRODATA 3 1 28000 001400 0
end
dwarf
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
sym y20 "go:info.main.SChan.Send$abstract" 0
sym y21 "" 0
sym y22 "go:info.main.SChan" 0
sym y23 "go:info.int" 0
dwfn y17 y18 y19 y20 y21 "main.SChan.Send" 1:86 1 0 1 74
dwdcl n1,n2,n4
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y20 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "main.SChan" 0 0 1 p2:86:7:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "int" 0 0 1 p2:86:21:0:0
dwname n4 1 1 1 0 0 0 -8 0 - - ? 0 0 ? p2:88:2:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "main.SChan" 0 0 1 p2:88:2:0:0
var 0 0 "c" 5 1 0 0 0 8 y22 "./closedchan.go" 86 7 0 0 1 0 v0
var 1 0 "x" 5 1 0 0 0 16 y23 "./closedchan.go" 86 21 0 1 1 0 v1
scope 0 0 - 0,1
dieref y17 2 y20 0
dieref y17 4 y20 1
dieoff y20 0:20,1:28
data y17 SDWARFFCN 29 0 0 0600000000000050019c29000000000000000029000000000000000000 6
reloc 1 4 R_DWARFSECREF 0 y20
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y20
reloc 15 4 R_DWARFSECREF 0 y18
reloc 20 4 R_DWARFSECREF 0 y20
reloc 24 4 R_DWARFSECREF 9 y18
data y18 SDWARFLOC 18 0 0 010000040024015000010000040020015100 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
data y19 SDWARFRANGE 0 0 0 - 0
data y21 SDWARFLINES 30 0 0 0009020000000000000000040203d000140a878906370661830220000101 1
reloc 3 8 R_ADDR 0 y1
data y20 SDWARFABSFCN 37 0 1 056d61696e2e534368616e2e53656e64000156012263000000000000227800000000000000 2
reloc 24 4 R_DWARFSECREF 0 y22
reloc 32 4 R_DWARFSECREF 0 y23
end
eof
"#

/-- The loaded `SChan.Send` (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load sendSsa sendProg

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

/-- The PC table `checkG6` gives (block `b2`: the index of each value's first Prog and of the
terminator's). -/
def tab : PcTab := [(2, [5, 5, 5, 5, 5, 7, 8, 10, 10, 10])]

/-- The class table `checkG6` gives: nothing known at the entry `b2`. -/
def kt : KTab := [(2, KMap.bot)]

/-- Block `b2`: the entry values `v6 = ArgIntReg` (`R0`), `v7 = ArgIntReg` (`R1`), `v2 = SP`,
`v1 = InitMem`; `v9 = MOVDstore {.autotmp_3} v2 v7 v1`, `v10 = MOVDaddr {.autotmp_3} v2` (`R1`),
`v12 = CALLstatic v6 v10 v9`, `v13 = SelectN [0] v12`, `v14 = MakeResult v13`; `Ret`. -/
def blk2 : Block := (lc.ctx.f.block? 2).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: GenG2's. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 32 8 ps.toList

/-- `ι`: GenG2's, and `.autotmp_3`'s block of activation 0 at `SP + 16`. -/
def ι6 (b : Blk) : Option (BitVec 64) :=
  if b = .temp 0 5 then some (GenG2.sp0 + 16) else GenG2.ι b

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0), no home slot,
the PC table of `checkG6`. -/
def E : MatchEnv :=
  { lc, ι := ι6, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The memory: `.autotmp_3`'s block, 8 poison bytes. -/
def mem1 : Mem := { blocks := #[(.temp 0 5, { data := Array.replicate 8 .poison })] }

/-- The `runLoc` state after the entry values: `x` in `R1`, every other register `poison`. -/
def s0 (x : BitVec 64) : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 1 then .i64 x else .poison,
    flags := .poison, slots := [], mem := .mem mem1 }

/-- The machine before `v9`: `X1 = x`, the activation's `g` and `FP`, the memory 0. -/
def m0 (x : BitVec 64) : MState :=
  { x := fun k => if k = 1 then x else if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 2 4, mem := fun _ => 0 }

/-- What compiled evaluation checks on `SChan.Send`: `checkG6` accepts it with `tab` and `kt` and
`checkG5` does not; `b2` holds `v9` and `v10` at 4 and 5 with their ops; `R1` holds a 64-bit
value after the entry values; the only accessed frame variable is `.autotmp_3` (aux 5), operand
`-8`, `NAME_AUTO`, of activation 0, at `frameOff 16`; there is no home slot; and `stepLoc` runs
`v9` and `v10`. -/
def sendFacts (x : BitVec 64) : Bool :=
  (checkG6 lc ps bs g).toOption == some (tab, kt) && (checkG5 lc ps bs g).toOption.isNone &&
    lc.ctx.f.blocks.toList.contains 2 && (lc.ctx.f.block? 2).isSome &&
    (lc.ctx.f.value? 9).isSome && (lc.ctx.f.value? 10).isSome &&
    blk2.values[4]? == some 9 && blk2.values[5]? == some 10 &&
    (val 9).op == .ARM64MOVDstore && (val 10).op == .ARM64MOVDaddr &&
    (kAt lc kt 2 blk2 4).get 1 == some 64 && accessedVars lc == [5] &&
    varOp g 5 == some (.AUTO, -8) && lc.ctx.act == 0 && (homeSlots lc).isEmpty &&
    decide (frameOff L .AUTO (-8) = 16) &&
    GenG1.okThen (stepLoc default lc (s0 x) (val 9)) fun s1 =>
      GenG1.okThen (stepLoc default lc s1 (val 10)) fun _ => true

/-- `checkG6` accepts `pallocSum.start` (`GenG3`) with G3's tables, and it accesses no frame
variable. -/
def startG6 : Bool :=
  (checkG6 GenG3.lc GenG3.ps GenG3.bs GenG3.g).toOption == some (GenG3.tab, GenG3.kt) &&
    (accessedVars GenG3.lc).isEmpty

theorem g6_facts : (sendFacts 7 && startG6) = true := by
  native_decide

theorem send_facts : sendFacts 7 = true := by
  have h := g6_facts
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem ι6_temp : ι6 (.temp 0 5) = some (GenG2.sp0 + 16) := by simp [ι6]

theorem ι6_ne {b : Blk} (h : b ≠ .temp 0 5) : ι6 b = GenG2.ι b := by simp [ι6, h]

theorem addrAgree6 : AddrAgree ι6 := by
  intro b n a hb ha hnt
  rw [ι6_ne (hnt 0 5)] at ha
  exact GenG2.addrAgree b n a hb ha hnt

theorem g6Env (hc : checkG6 lc ps bs g = .ok (tab, kt)) (hsl : (homeSlots lc).isEmpty = true)
    (hvs : accessedVars lc = [5]) (hvo : varOp g 5 = some (.AUTO, -8)) (hact : lc.ctx.act = 0)
    (hoff : frameOff L .AUTO (-8) = 16) : G6Env lc g L ps 0 tab E where
  env := {
    lcEq := rfl
    link := rfl
    pcOf := rfl
    retOut := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG6_spec hc
      intro p hp
      exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
    addr := addrAgree6
    glob := fun _ _ _ _ => by simp [E, ι6, GenG2.ι]; rfl
    syms := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG6_spec hc
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
    intro x hx o ho _
    rw [hvs, List.mem_singleton] at hx
    subst hx
    rw [hvo] at ho
    cases ho
    rw [hact, hoff]
    show ι6 (.temp 0 5) = some (GenG2.sp0 + BitVec.ofInt 64 16)
    rw [ι6_temp]
    rfl

theorem memInj1 : MemInj ι6 mem1 (fun _ => 0) where
  nil := by simp [ι6, GenG2.ι]
  mapped := by
    intro b al h
    simp [mem1] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨GenG2.sp0 + 16, ι6_temp, fun _ => by decide, by decide⟩
  inj := by
    intro b al b' al' a a' h h' hne
    simp [mem1] at h h'
    exact absurd (h.1.trans h'.1.symm) hne
  bytes := ⟨fun _ _ => False, by
    intro b al a h _
    simp [mem1] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun o ho => ho.elim, fun o _ ho => ho.elim, fun i hi _ => ?_⟩
    simp [ByteRel]⟩

theorem keys1 : KeysNodup mem1 := by simp [KeysNodup, mem1]

theorem sep1 : SepFrom ι6 (StkAt E) mem1 := by
  intro b al a hb hι y hy
  simp [mem1] at hb
  obtain ⟨rfl, rfl⟩ := hb
  rw [ι6_temp] at hι
  cases hι
  rcases hy with ⟨-, h1, h2⟩ | ⟨k, off, h, -⟩
  · simp only [E, GenG2.sp0] at h1 h2
    simp only [GenG2.sp0, Array.size_replicate]
    rintro ⟨h3, -⟩
    have : (0x7fff0000 + 16 : BitVec 64).toNat = 0x7fff0010 := by decide
    rw [this] at h3
    have : (0x7fff0000 : BitVec 64).toNat = 0x7fff0000 := by decide
    rw [this] at h2
    omega
  · simp [E] at h

theorem locMatch0 (x : BitVec 64) : LocMatch E (s0 x) 2 4 (m0 x) where
  regs := by
    intro r v hv
    simp only [s0, Array.getElem?_ofFn] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · split at hv
        · subst hv
          rename_i h1
          subst h1
          simp only [objX?] at hk
          cases hk
          exact Or.inl rfl
        · subst hv; trivial
      · split at hv
        · rename_i h1; subst h1; simp [objV?] at hk
        · subst hv; trivial
    · cases hv
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem1, rfl, memInj1⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g6Inv0 (x : BitVec 64) {K : KMap} (h1 : K.get 1 = some 64) : G3Inv E lc K (s0 x) where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem1, rfl, keys1, sep1⟩
    simp only [s0, Array.getElem?_ofFn] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      split at hv
      · rename_i h1'
        subst hv; subst h1'
        rw [h1] at hc; cases hc; rfl
      · subst hv; trivial
    · cases hv
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of a value that is no compare, load, pair load or subtraction. -/
theorem g6Pre_of {v : Value} (h1 : v.op ≠ .ARM64CMP) (h2 : v.op ≠ .ARM64CMPconst)
    (h3 : loadOp? v.op = none) (h4 : v.op ≠ .ARM64LDP) (h5 : v.op ≠ .ARM64SUB) (s : LocState) :
    G4Pre lc s v :=
  ⟨⟨fun h => by rcases h with h | h <;> contradiction,
    (fun _ _ _ hl => by rw [h3] at hl; cases hl), fun h => absurd h h5⟩, fun h => absurd h h4⟩

/-- **G6 on `SChan.Send`**: from the state after the entry values (`R1 = 7`), the store `v9` of
`x` to the frame variable `.autotmp_3` (`MOVD R1, -8(RSP)`) and its address `v10`
(`MOVD $-8(RSP), R1`) are matched by a machine run of the Progs to a state related before `v12`,
with the registers at their classes, under an activation that extends `E` and is a `G6Env`. -/
theorem genG6_value_witness :
    ∃ s1 s2 E' m2, stepLoc default lc (s0 7) (val 9) = .ok s1 ∧
      stepLoc default lc s1 (val 10) = .ok s2 ∧ E.Extends E' ∧ G6Env lc g L ps 0 tab E' ∧
      PStar GenG2.H0 L ps.toList 0 (m0 7) m2 ∧ LocMatch E' s2 2 6 m2 ∧
      G3Inv E' lc (kAt lc kt 2 blk2 6) s2 := by
  have hf := send_facts
  simp only [sendFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem,
    decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, -⟩, hmem⟩, hbs⟩, hv9s⟩, hv10s⟩, hi4⟩, hi5⟩, hop9⟩, hop10⟩, hk1⟩,
    hvs⟩, hvo⟩, hact⟩, hsl⟩, hoff⟩, hrun⟩ := hf
  have hc : checkG6 lc ps bs g = .ok (tab, kt) := by
    revert hck; cases checkG6 lc ps bs g <;> simp [Except.toOption]
  have hb : lc.ctx.f.block? 2 = some blk2 := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk2, hb]
  have hval : ∀ n, (lc.ctx.f.value? n).isSome = true → lc.ctx.f.value? n = some (val n) := by
    intro n h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    simp [val, hv]
  have hE := g6Env hc hsl hvs hvo hact hoff
  obtain ⟨s1, hs1, hrun⟩ := GenG1.okThen_spec hrun
  obtain ⟨s2, hs2, -⟩ := GenG1.okThen_spec hrun
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, hinv1⟩ := g6_value (H := GenG2.H0) hc hE hmem hb hi4
    (hval 9 hv9s) (by rw [hop9]; rfl) (locMatch0 7) (g6Inv0 7 hk1)
    (g6Pre_of (by rw [hop9]; decide) (by rw [hop9]; decide)
      (by rw [hop9]; simp [loadOp?, narrowLoad?]) (by rw [hop9]; decide) (by rw [hop9]; decide) _)
    (GenG2.callOK_ne (by rw [hop9]; decide)) hs1
  obtain ⟨E2, m2, hx2, hE2, hp2, hm2, hinv2⟩ := g6_value (H := GenG2.H0) hc hE1 hmem hb hi5
    (hval 10 hv10s) (by rw [hop10]; rfl) hm1 hinv1
    (g6Pre_of (by rw [hop10]; decide) (by rw [hop10]; decide)
      (by rw [hop10]; simp [loadOp?, narrowLoad?]) (by rw [hop10]; decide) (by rw [hop10]; decide)
      _)
    (GenG2.callOK_ne (by rw [hop10]; decide)) hs2
  exact ⟨s1, s2, E2, m2, hs1, hs2, MatchEnv.Extends.trans hx1 hx2, hE2, hp1.trans hp2, hm2, hinv2⟩

/-- **G6 on `pallocSum.start`**: `g6_term` on the bit test `TBNZ [63]` (bit 63 of `x = 7` clear)
gives a machine run to a state related before the first value of `b2`, with the registers at its
classes. -/
theorem genG6_term_witness :
    ∃ s1 e m1, stepTermLoc GenG3.lc (GenG2.s0 7) GenG3.blk1 = .ok (.goto e, s1) ∧ e.b = 2 ∧
      PStar GenG2.H0 GenG3.L GenG3.ps.toList 0 (GenG3.m0 7) m1 ∧ LocMatch GenG3.E s1 2 0 m1 ∧
      G3Inv GenG3.E GenG3.lc (GenG3.kt.at 2) s1 := by
  have h := g6_facts
  simp only [Bool.and_eq_true] at h
  have h2 := h.2
  simp only [startG6, Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨hres6, hnv⟩ := h2
  have hc6 : checkG6 GenG3.lc GenG3.ps GenG3.bs GenG3.g = .ok (GenG3.tab, GenG3.kt) := by
    revert hres6; cases checkG6 GenG3.lc GenG3.ps GenG3.bs GenG3.g <;> simp [Except.toOption]
  have hf := GenG3.g3_facts
  simp only [Bool.and_eq_true] at hf
  have hf1 := hf.1
  simp only [GenG3.startFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hsl⟩, hnc⟩, hm1⟩, -⟩, hb1s⟩, -⟩, -⟩, hsz⟩, hkind⟩,
    -⟩, -⟩, hk0⟩, hrun⟩ := hf1
  have hc3 : checkG3 GenG3.lc GenG3.ps GenG3.bs GenG3.g = .ok (GenG3.tab, GenG3.kt) := by
    revert hres; cases checkG3 GenG3.lc GenG3.ps GenG3.bs GenG3.g <;> simp [Except.toOption]
  have hb1 : GenG3.lc.ctx.f.block? 1 = some GenG3.blk1 := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [GenG3.blk1, hb]
  have hE : G6Env GenG3.lc GenG3.g GenG3.L GenG3.ps 0 GenG3.tab GenG3.E :=
    ⟨GenG3.g3Env hc3 hsl hnc, fun x hx => by simp [List.isEmpty_iff.1 hnv] at hx⟩
  obtain ⟨⟨n, s1⟩, hs1, hrun⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨hgo, -⟩ := hrun
  obtain ⟨e, rfl, het⟩ := GenG1.gotoIs_spec hgo
  obtain ⟨m1, hp1, hlm1, hinv1, -⟩ := g6_term (H := GenG2.H0) hc6 hE hm1 hb1
    (GenG3.locMatch0 7) (GenG3.g3Inv0 7 (by rw [hsz]; exact hk0))
    (fun hz => by rw [hkind] at hz; rcases hz with h | h <;> cases h) hs1
  exact ⟨s1, e, m1, hs1, het, hp1, het ▸ hlm1, het ▸ hinv1⟩

end GoFV.Proof.Witness.GenG6
