import GoFV.Proof.Gen.G7
import GoFV.Proof.Witness.GenG4

/-!
# Non-vacuity witness: slice G7 of the genssa validator on `(*A).g` of `test/method`

`test/method/main/(*A).g,1.ssa` and `test/method/main/(*A).g,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`gSsa`, `gProg`): the wrapper Go
generates for the method `g` promoted to `*A` from its embedded field (`test/method.go`):

```go
type A struct{ B }
type B struct {
	C
	*D
}
type C int

func (*C) g() {} // pointer receiver
```

`checkG6` rejects it (the nil check `v6 = LoweredNilCheck v5 v1` of the receiver); `checkG7`
accepts it with the PC table `tab` and the class table `kt` (nothing known at the entry): `v6` is
`MOVB (R0), R27`. By compiled evaluation (`native_decide`, listed in
`scripts/axioms-allowlist.txt`; `g7_facts`), from the state after the entry values (the receiver
in `R0`), `stepLoc` runs `v6` when the receiver points to a global `s` (`GenG4.memS`) and panics
when it is nil. On a frameless activation with `G6Env` (`SP = 0x7fff0000`, every symbol at
`2^40`, `ι` the nil block and the globals there, the Progs at `0x10000 + 4·ID`, `ret = 0`),
`g7_value` gives a machine run of the Progs past `MOVB (R0), R27` to a state related before
`v11` (`genG7_value_witness`), and `g7_nilPanic` a run to the `MOVB` that faults in the nil page,
a panicking `runProg` with the same `nilDeref` (`genG7_panic_witness`).
-/

namespace GoFV.Proof.Witness.GenG7

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/method/main/(*A).g,1.ssa` (quick-v10). -/
def gSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "(*A).g" 1 0 0
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
type t5 INT 8 8 0 comparable,named "C" "main.C"
type t7 INT 8 8 0 comparable,named "D" "main.D"
type t6 PTR 8 8 8 hasptr,direct,comparable "*D" "*main.D" t7
type t4 STRUCT 16 8 16 hasptr,comparable,named "B" "main.B" 2
field 0 "C" t5 0 1
field 1 "D" t6 8 1
type t3 STRUCT 16 8 16 hasptr,comparable,named "A" "main.A" 1
field 0 "B" t4 0 1
type t2 PTR 8 8 8 hasptr,direct,comparable "*A" "*main.A" t3
type t1 FUNC 8 8 8 hasptr,direct "method(*A) func()" "method(*main.A) func()" 1 0 0
field 0 "" t2 ? 0
aux a2 sym "main.(*A).g" "main.(*A).g" 1 - 0 - - - - 0
posbase p2 "./method.go" 1 1 -1
aux a3 name "~p0" "~p0" PPARAM t2 0 1 used p2:262:7:0:0
aux a1 call "AuxCall{main.(*A).g}" a2 1 1 0 8 8 1 0
abiparam in 0 t2 a3 0 0
type t8 BOOL 1 1 0 comparable,named "bool" "bool"
type t9 INT8 1 1 0 comparable,named "int8" "int8"
type t10 INT16 2 2 0 comparable,named "int16" "int16"
type t11 INT32 4 4 0 comparable,named "int32" "int32"
type t12 INT64 8 8 0 comparable,named "int64" "int64"
type t13 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t14 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t15 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t16 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t17 INT 8 8 0 comparable,named "int" "int"
type t18 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t19 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t20 UINT 8 8 0 comparable,named "uint" "uint"
type t21 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t22 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t23 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t13
type t24 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t11
type t25 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t15
type t26 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t17
type t27 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t21
type t28 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t18
type t29 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t19
type t30 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t23
type t31 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t32 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t33 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t34 SSA ? ? ? - "mem" ""
type t35 SSA ? ? ? - "flags" ""
type t36 SSA ? ? ? - "void" ""
type t37 SSA 16 8 ? - "int128" ""
type t38 RESULTS ? ? ? - "mem" "" 1 t34
posbase p1 "<autogenerated>" 1 1 -1
type t39 PTR 8 8 8 hasptr,direct,comparable "**A" "**main.A" t2
type t40 PTR 8 8 8 hasptr,direct,comparable "*B" "*main.B" t4
type t41 PTR 8 8 8 hasptr,direct,comparable "*C" "*main.C" t5
slot s1 a3 t2 0 - 0
posbase p148 "./method.go" 1 1 145
aux a4 name "~p0" "~p0" PAUTO t41 0 1 - p148:262:7:0:0
slot s2 a4 t41 0 - 0
f b1 t1 a1 11 2
typs Bool=t8,Int8=t9,Int16=t10,Int32=t11,Int64=t12,UInt8=t13,UInt16=t14,UInt32=t15,UInt64=t16,Int=t17,Float32=t18,Float64=t19,UInt=t20,Uintptr=t21,String=t22,BytePtr=t23,Int32Ptr=t24,UInt32Ptr=t25,IntPtr=t26,UintptrPtr=t27,Float32Ptr=t28,Float64Ptr=t29,BytePtrPtr=t30,Complex64=t31,Complex128=t32,UnsafePtr=t33,Mem=t34,Flags=t35,Void=t36,Int128=t37,ResultMem=t38
b b1 Plain p1:1:0:0:0 0 0 - - b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 4 -
v v2 SP t21 0 - p0:0:0:0:0 1 -
v v3 SB t21 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t39 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:0:0 1 v5,v1
v v7 OffPtr t40 0 - p1:1:0:0:0 1 v6
v v8 OffPtr t41 0 - p1:1:0:0:0 0 v7
v v9 InlMark t36 145 - p1:1:0:1:0 0 v1
b b2 Ret p1:1:0:0:0 0 0 - v11 - b1:0
v v10 Copy t34 0 - p1:1:0:2:0 1 v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v10
names s1,s2
named s1 v5
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 11 2
b b1 Plain p1:1:0:0:0 0 0 - - b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 4 -
v v2 SP t21 0 - p0:0:0:0:0 1 -
v v3 SB t21 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t39 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 1 v5,v1
v v7 OffPtr t40 0 - p1:1:0:0:0 1 v6
v v8 OffPtr t41 0 - p1:1:0:0:0 0 v7
v v9 InlMark t36 145 - p1:1:0:0:0 0 v1
b b2 Ret p1:1:0:0:0 0 0 - v11 - b1:0
v v10 Copy t34 0 - p1:1:0:2:0 1 v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v10
names s1,s2
named s1 v5
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev -
freeb -
cache postorder b2,b1
cache linestarts 1:1:1
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 11 2
b b1 Plain p1:1:0:0:0 0 0 - - b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v2 SP t21 0 - p0:0:0:0:0 1 -
v v3 SB t21 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t39 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 1 v5,v1
v v7 OffPtr t40 0 - p1:1:0:0:0 1 v6
v v8 OffPtr t41 0 - p1:1:0:0:0 0 v7
v v9 InlMark t36 145 - p1:1:0:0:0 0 v1
b b2 Ret p1:1:0:0:0 0 0 - v11 - b1:0
v v10 Copy t34 0 - p1:1:0:2:0 0 v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1,s2
named s1 v5
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev -
freeb -
cache postorder b2,b1
cache linestarts 1:1:1
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 11 2
b b1 Plain p1:1:0:0:0 0 0 - - b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
b b2 Ret p1:1:0:0:0 0 0 - v11 - b1:0
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb -
cache postorder b2,b1
cache linestarts 1:1:1
dcllen 2
end
pass 4 "short circuit"
f b2 t1 a1 11 2
b b1 BlockInvalid p1:1:0:0:0 0 0 - - - -
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb -
cache linestarts 1:1:1
dcllen 2
end
pass 5 "decompose user"
f b2 t1 a1 11 2
b b1 BlockInvalid p1:1:0:0:0 0 0 - - - -
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb -
cache linestarts 1:1:1
dcllen 2
end
pass 6 "pre-opt deadcode"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache linestarts 1:1:1
dcllen 2
end
pass 7 "opt"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache linestarts 1:1:1
dcllen 2
end
pass 8 "zero arg cse"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache linestarts 1:1:1
dcllen 2
end
pass 9 "opt deadcode"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache linestarts 1:1:1
dcllen 2
end
pass 10 "generic cse"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 11 "phiopt"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 12 "gcse deadcode"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 13 "nilcheckelim"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 14 "prove"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 15 "divisible"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 16 "divmod"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 17 "middle opt"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 18 "known bits"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 19 "early fuse"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v10,v9,v8,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "~p0+0" a3 0
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
v v10 SB t21 0 - p0:0:0:0:0 0 -
v v9 SP t21 0 - p0:0:0:0:0 1 -
v v8 OffPtr t39 0 - p0:0:0:0:0 0 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts 0=v8
freev v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 21 "decompose builtin"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
v v10 SB t21 0 - p0:0:0:0:0 0 -
v v9 SP t21 0 - p0:0:0:0:0 1 -
v v8 OffPtr t39 0 - p0:0:0:0:0 0 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts 0=v8
freev v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 22 "softfloat"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
v v10 SB t21 0 - p0:0:0:0:0 0 -
v v9 SP t21 0 - p0:0:0:0:0 1 -
v v8 OffPtr t39 0 - p0:0:0:0:0 0 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts 0=v8
freev v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 23 "branchelim"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
v v10 SB t21 0 - p0:0:0:0:0 0 -
v v9 SP t21 0 - p0:0:0:0:0 1 -
v v8 OffPtr t39 0 - p0:0:0:0:0 0 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts 0=v8
freev v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 24 "late opt"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 25 "dead auto elim"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 26 "sccp"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 27 "generic deadcode"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 28 "late fuse"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 29 "check bce"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 30 "dse"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 31 "memcombine"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 32 "writebarrier"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 NilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 33 "lower"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 34 "addressing modes"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 35 "late lower"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 36 "pair"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 38 "lowered cse"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 2
end
pass 39 "elim unread autos"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 2
end
pass 40 "tighten tuple selectors"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 2
end
pass 41 "lowered deadcode"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 2
end
pass 42 "checkLower"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 2
end
pass 43 "loop invariant"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 2
end
pass 44 "late phielim and copyelim"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 2
end
pass 45 "tighten"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 2
end
pass 46 "late deadcode"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 2
end
pass 47 "critical"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 2
end
pass 48 "phi tighten"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 2
end
pass 49 "likelyadjust"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
dcllen 2
end
pass 50 "layout"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v6 ARM64LoweredNilCheck t36 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v6 ARM64LoweredNilCheck t36 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v6 ARM64LoweredNilCheck t36 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v8,v9,v10,v7,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v6 ARM64LoweredNilCheck t36 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v2,v3,v4,v7,v8,v9,v10
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 6 v5:R0
dcllen 2
end
pass 55 "loop rotate"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v6 ARM64LoweredNilCheck t36 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v2,v3,v4,v7,v8,v9,v10
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 6 v5:R0
dcllen 2
end
pass 56 "trim"
f b2 t1 a1 11 2
b b2 Ret p1:1:0:0:0 0 0 - v11 - -
v v5 ArgIntReg t2 0 a5 p1:1:0:0:0 1 -
v v1 InitMem t34 0 - p0:0:0:0:0 2 -
v v6 ARM64LoweredNilCheck t36 0 - p1:1:0:1:0 0 v5,v1
v v11 MakeResult t38 0 - p1:1:0:0:0 1 v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a4/t41/0/-/0=s2
consts -
freev v2,v3,v4,v7,v8,v9,v10
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 6 v5:R0
dcllen 2
end
frontend
end
ptrcache t3,t5,t7,t10,t11,t12,t13,t15,t17,t18,t19,t21,t22,t23,t30
typelink t34=t38
typeorder t9,t13,t10,t14,t11,t15,t12,t16,t5,t7,t17,t20,t21,t31,t32,t18,t19,t8,t23,t24,t25,t41,t6,t26,t27,t28,t29,t30,t39,t2,t40,t1,t3,t4,t22,t33,t34,t36,t35,t37,t38
eof
"#

/-- `test/method/main/(*A).g,1.prog` (quick-v10). -/
def gProg : String := r#"gofv-prog 3
pkg "main"
func "(*A).g" 1
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
type t1 8 8 8 1 01 "*A"
name n1 "~p0" PPARAM t1 1 "main.~p0" 0 a3
type t2 8 8 8 1 01 "*C"
name n2 "~p0" PAUTO t2 1 "main.~p0" 0 a4
in n1 0 used
in n2 0 -
out n1 0 used
opt n2 0 -
stack 0 0 8
end
genin
posbase p1 "<autogenerated>" 1 1 -1 0 "<autogenerated>" "<autogenerated>" 1 1
sym y1 "main.(*A).g" 1
curfn p1:1:0:0:0 0 0
regargs 8192:0:t1
text y1 0 0 23 0 1 200091
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "main.(*A).g.arginfo1" 0
sym y5 "main.(*A).g.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p1:1:0:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p1:1:0:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p1:1:0:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p1:1:0:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p1:1:0:2:0
p 6 6 0 0 0 - MOVB 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8219/0/0/NONE/0/0/-/- 0 0 p1:1:0:1:0
p 7 7 0 0 0 - RET 0 _ 0 - _ 0 0 p1:1:0:0:0
p 8 8 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 23 0 1 200091
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 2
dbgslot 0 n1 t1 0
dbgregout -
dbgpc -
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
p 9 0 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p1:1:0:2:0
p 6 0 0 0 294 - MOVB 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8219/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 10 4 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p1:1:0:1:0
p 7 4 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p1:1:0:0:0
fn y1 8 0 23 0 1 2000d9
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 16 0 1b008039c0035fd60000000000000000 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y3,_,_,_,y4,y5
usedfiles 0
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y6 SRODATA 5 1 28000 0101020300 0
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
posbase p2 "./method.go" 1 1 -1 1 "./method.go" "./method.go" 1 1
sym y18 "main.(*C).g" 1
inl i145 - p1:1:0:0:0 y18 "(*C).g"
posbase p148 "./method.go" 1 1 145 1 "./method.go" "./method.go" 1 1
sym y19 "go:info.main.(*C).g$abstract" 0
sym y20 "go:info.*main.A" 0
dwfn y14 y15 y16 - y17 "main.(*A).g" 0:1 1 1 1 51
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwinlfn y18 y19
dwinldcl y18 "~p0" 0 p2:262:7:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "*main.A" 0 0 1 p2:262:7:0:0
dwname n2 1 0 0 1 0 0 0 0 - - "*main.C" 0 0 1 p148:262:7:0:0
var 0 0 "~p0" 5 0 0 0 0 8 y20 "./method.go" 262 7 0 0 0 0 -
scope 0 0 - 0
data y14 SDWARFFCN 34 0 0 046d61696e2e282a41292e67000010019c012e7e7030000086020000000002910800 2
reloc 13 1 R_DWTXTADDR_U1 0 y1
reloc 26 4 R_DWARFSECREF 0 y20
data y15 SDWARFLOC 0 0 0 - 0
data y16 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 16 0 0 00090200000000000000000210000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded `(*A).g` (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load gSsa gProg

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

/-- The PC table `checkG7` gives (block `b2`: the index of each value's first Prog and of the
terminator's; `v6` from the `PCDATA` at 5 through the `MOVB` at 6). -/
def tab : PcTab := [(2, [5, 5, 5, 7, 7])]

/-- The class table `checkG7` gives: nothing known at the entry `b2`. -/
def kt : KTab := [(2, KMap.bot)]

/-- Block `b2`: the entry values `v5 = ArgIntReg` (`R0`) and `v1 = InitMem`; `v6 = LoweredNilCheck
v5 v1`, `v11 = MakeResult v1`; `Ret`. -/
def blk2 : Block := (lc.ctx.f.block? 2).getD default

def v6 : Value := (lc.ctx.f.value? 6).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, no frame, every symbol at `symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 0 0 ps.toList

/-- A frameless activation (`SP = 0x7fff0000`, `g = 0x9000`, `LR = 0x40`, `FP = 0`) with the
globals at their symbols and the PC table of `checkG7`. -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := 0x7fff0000, slot := fun _ => none, g := 0x9000, lr := 0x40, fp := 0,
    framed := false, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The nil pointer. -/
def nilP : Ptr := ⟨.nil, 0⟩

/-- The `runLoc` state after the entry values: the receiver `p` in `R0`, every other register
`poison`, the memory `GenG4.memS` (a global `s` of 16 zero bytes). -/
def s0 (p : Ptr) : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG4.memS },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .ptr p else .poison,
    flags := .poison, slots := [], mem := .mem GenG4.memS }

/-- The machine before `v6`: `X0 = x`, the activation's `g`, `FP`, `LR`, the memory 0. -/
def m0 (x : BitVec 64) : MState :=
  { x := fun k => if k = 0 then x else if k = 28 then 0x9000 else if k = 29 then 0 else
      if k = 30 then 0x40 else 0,
    sp := 0x7fff0000, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 2 2, mem := fun _ => 0 }

/-- A `runLoc` step that panics. -/
def isPanic (r : Res LocState) : Bool :=
  match r with
  | .panic .nilDeref _ => true
  | _ => false

theorem isPanic_spec {r : Res LocState} (h : isPanic r = true) : ∃ mm, r = .panic .nilDeref mm := by
  unfold isPanic at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- What compiled evaluation checks on `(*A).g`: `checkG7` accepts it with `tab` and `kt` and
`checkG6` does not; it accesses no frame variable, has no home slot and no static call; `b2` holds
`v6` at 2, a nil check of `v5`; `R0` holds a 64-bit value after the entry values; a pointer to `s`
read from `v5` points to a byte of `memS`; `stepLoc` runs `v6` on a pointer to `s` and panics with
`nilDeref` on the nil pointer. -/
def gFacts : Bool :=
  (checkG7 lc ps bs g).toOption == some (tab, kt) && (checkG6 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty && GenG2.noCalls lc &&
    lc.ctx.f.blocks.toList.contains 2 && (lc.ctx.f.block? 2).isSome &&
    (lc.ctx.f.value? 6).isSome && blk2.values[2]? == some 6 &&
    v6.op == .ARM64LoweredNilCheck && v6.args[0]? == some 5 &&
    (kAt lc kt 2 blk2 2).get 0 == some 64 &&
    GenG1.okThen ((s0 GenG4.ptrS).read lc 5) (fun x =>
      (Arm64.addr x 0#64).all fun p => (GenG4.memS.read p 1).isSome) &&
    GenG1.okThen (stepLoc default lc (s0 GenG4.ptrS) v6) (fun _ => true) &&
    isPanic (stepLoc default lc (s0 nilP) v6)

theorem g7_facts : gFacts = true := by
  native_decide

theorem g7Env (hc : checkG7 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) (hnc : GenG2.noCalls lc = true) :
    G6Env lc g L ps 0 tab E where
  env := {
    lcEq := rfl
    link := rfl
    pcOf := rfl
    retOut := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG7_spec hc
      intro p hp
      exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
    addr := GenG2.addrAgree
    glob := fun _ _ _ _ => rfl
    syms := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG7_spec hc
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
    intro x hx
    simp [List.isEmpty_iff.1 hav] at hx

theorem sepS : SepFrom GenG2.ι (StkAt E) GenG4.memS := by
  intro b al a _ _ y hy
  rcases hy with ⟨h1, -⟩ | ⟨k, off, h, -⟩
  · cases h1
  · cases h

/-- `s0 p` and `m0 x` before `v6`, when `x` is `p`'s injected address. -/
theorem locMatch0 (p : Ptr) (x : BitVec 64) (hx : PtrRel GenG2.ι p x) :
    LocMatch E (s0 p) 2 2 (m0 x) where
  regs := by
    intro r v hv
    simp only [s0, Array.getElem?_ofFn] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · split at hv
        · subst hv
          rename_i h0
          subst h0
          simp only [objX?] at hk
          cases hk
          exact hx
        · subst hv; trivial
      · split at hv
        · rename_i h0; subst h0; simp [objV?] at hk
        · subst hv; trivial
    · cases hv
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG4.memS, rfl, GenG4.memInjS⟩
  frame := ⟨rfl, rfl, (fun h => by cases h), fun _ => ⟨rfl, rfl⟩⟩
  pc := rfl

theorem g7Inv0 (p : Ptr) {K : KMap} (h0 : K.get 0 = some 64) : G3Inv E lc K (s0 p) where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG4.memS, rfl, GenG4.keysS, sepS⟩
    simp only [s0, Array.getElem?_ofFn] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      split at hv
      · rename_i h0'
        subst hv; subst h0'
        rw [h0] at hc; cases hc; rfl
      · subst hv; trivial
    · cases hv
  slots := by intro k v h; simp [s0] at h

/-- The facts of `g7_facts` as hypotheses. -/
theorem facts :
    checkG7 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ GenG2.noCalls lc = true ∧
      2 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 2 = some blk2 ∧
      lc.ctx.f.value? 6 = some v6 ∧ blk2.values[2]? = some 6 ∧
      v6.op = .ARM64LoweredNilCheck ∧ v6.args[0]? = some 5 ∧
      (kAt lc kt 2 blk2 2).get 0 = some 64 ∧
      GenG1.okThen ((s0 GenG4.ptrS).read lc 5) (fun x =>
        (Arm64.addr x 0#64).all fun p => (GenG4.memS.read p 1).isSome) = true ∧
      GenG1.okThen (stepLoc default lc (s0 GenG4.ptrS) v6) (fun _ => true) = true ∧
      isPanic (stepLoc default lc (s0 nilP) v6) = true := by
  have hf := g7_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hnc⟩, hm2⟩, hb2s⟩, hv6s⟩, hi2⟩, hop⟩, harg⟩,
    hk0⟩, hread⟩, hrun⟩, hpan⟩ := hf
  refine ⟨?_, hav, hsl, hnc, hm2, ?_, ?_, hi2, hop, harg, hk0, hread, hrun, hpan⟩
  · revert hres; cases checkG7 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb2s
    simp [blk2, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv6s
    simp [v6, hv]

/-- **G7 on `(*A).g`, the receiver points to `s`**: from the state after the entry values, the nil
check `v6` (`MOVB (R0), R27`) is matched by a machine run of the Progs to a state related before
`v11`, with the registers at their classes. -/
theorem genG7_value_witness :
    ∃ s1 E' m1, stepLoc default lc (s0 GenG4.ptrS) v6 = .ok s1 ∧ E.Extends E' ∧
      G6Env lc g L ps 0 tab E' ∧ PStar GenG2.H0 L ps.toList 0 (m0 GenG2.symA) m1 ∧
      LocMatch E' s1 2 3 m1 ∧ G3Inv E' lc (kAt lc kt 2 blk2 3) s1 := by
  obtain ⟨hc, hav, hsl, hnc, hm2, hb, hv, hi2, hop, harg, hk0, hread, hrun, -⟩ := facts
  obtain ⟨s1, hs1, -⟩ := GenG1.okThen_spec hrun
  have hE := g7Env hc hav hsl hnc
  have hpre : G7Pre lc (s0 GenG4.ptrS) v6 := by
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, fun _ a x ha hx p hp _ => ?_⟩
    · intro h
      rcases h with h | h <;> rw [hop] at h <;> cases h
    · intro _ _ _ hl
      rw [hop] at hl
      cases hl
    · intro h
      rw [hop] at h
      cases h
    · intro h
      rw [hop] at h
      cases h
    rw [harg] at ha
    cases ha
    obtain ⟨x', hx', hall⟩ := GenG1.okThen_spec hread
    rw [hx] at hx'
    cases hx'
    rw [hp] at hall
    exact ⟨GenG4.memS, rfl, by simpa using hall⟩
  obtain ⟨E', m1, hx, hE', hp, hlm, hinv⟩ := g7_value (H := GenG2.H0) (env := default) hc hE hm2
    hb hi2 hv (by rw [hop]; rfl) (locMatch0 GenG4.ptrS GenG2.symA ⟨GenG2.symA, rfl, by decide⟩)
    (g7Inv0 _ hk0) hpre
    (GenG2.callOK_ne (by rw [hop]; nofun)) hs1
  exact ⟨s1, E', m1, hs1, hx, hE', hp, hlm, hinv⟩

/-- **G7 on `(*A).g`, the receiver is nil**: `runLoc` panics with `nilDeref` at the nil check
`v6`, and a machine run of the Progs reaches its `MOVB (R0), R27`, which faults in the nil page:
`runProg` panics with `nilDeref`. -/
theorem genG7_panic_witness :
    ∃ mm m1, stepLoc default lc (s0 nilP) v6 = .panic .nilDeref mm ∧
      PStar GenG2.H0 L ps.toList 0 (m0 0) m1 ∧ PPanics GenG2.H0 L ps.toList 0 m1 .nilDeref ∧
      ∃ m2, GoFV.Arm64.runProg GenG2.H0 L ps.toList 0 1 m1 = .panicked .nilDeref m2 := by
  obtain ⟨hc, hav, hsl, hnc, hm2, hb, hv, hi2, hop, -, hk0, -, -, hpan⟩ := facts
  obtain ⟨mm, hs⟩ := isPanic_spec hpan
  obtain ⟨-, m1, hp, hpp⟩ := g7_nilPanic (H := GenG2.H0) (env := default)
    hc (g7Env hc hav hsl hnc) hm2 hb hi2 hv hop (locMatch0 nilP 0 ⟨0, rfl, by decide⟩)
    (g7Inv0 _ hk0) hs
  exact ⟨mm, m1, hs, hp, hpp, hpp.runProg 0⟩

end GoFV.Proof.Witness.GenG7
