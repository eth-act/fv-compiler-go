import GoFV.Proof.Gen.G4
import GoFV.Proof.Witness.GenG3

/-!
# Non-vacuity witness: slice G4 of the genssa validator on `(*errorString).Error`

`std/errors/(*errorString).Error,1.ssa` and `std/errors/(*errorString).Error,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`errSsa`, `errProg`):

```go
func (e *errorString) Error() string {
	return e.s
}
```

`checkG3` rejects it (the pair load `v15 = LDP v6 v1`, emitted `LDP (R0), (R0, R1)`); `checkG4`
accepts it with the PC table `tab` and the class table `kt` (nothing known at the entry). By
compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g4_facts`), from
the state after the entry values (`e` in `R0`, a pointer to the 16 zero bytes of a global `s`),
`stepLoc` runs `v15`, `v14 = Select1 v15` (`R1`) and `v13 = Select0 v15` (`R0`), and the pair load
reads valid bytes at both addresses. On a frameless activation with `G2Env` (`SP = 0x7fff0000`,
every symbol and `s` at `2^40`, the Progs at `0x10000 + 4·ID`, `ret = 0`), `g4_value` gives a
machine run of the Progs past the three values to a state related before `v11`, with the
registers at their classes (`genG4_value_witness`). `checkG4` also accepts `pallocSum.start`
(`GenG3`) with G3's tables; there `g4_term` runs the bit test `TBNZ [63]` to `b2`
(`genG4_term_witness`).
-/

namespace GoFV.Proof.Witness.GenG4

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/errors/(*errorString).Error,1.ssa` (quick-v10). -/
def errSsa : String := r#"gofv-ssa 5.1
pkg "errors"
func "(*errorString).Error" 1 0 0
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
config localpkg "errors"
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
type t4 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t3 STRUCT 16 8 8 hasptr,comparable,named "errorString" "errors.errorString" 1
field 0 "s" t4 0 0
type t2 PTR 8 8 8 hasptr,direct,comparable "*errorString" "*errors.errorString" t3
type t1 FUNC 8 8 8 hasptr,direct "method(*errorString) func() string" "method(*errors.errorString) func() string" 1 0 1
field 0 "e" t2 ? 0
field 1 "" t4 ? 0
aux a2 sym "errors.(*errorString).Error" "errors.(*errorString).Error" 1 - 0 - - - - 0
posbase p2 "errors/errors.go" 1 1 -1
aux a3 name "e" "e" PPARAM t2 0 1 used p2:73:7:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t4 0 1 - p2:73:31:0:0
aux a1 call "AuxCall{errors.(*errorString).Error}" a2 1 1 1 8 8 1 2
abiparam in 0 t2 a3 0 0
abiparam out 0 t4 a4 0,1 -1
type t5 BOOL 1 1 0 comparable,named "bool" "bool"
type t6 INT8 1 1 0 comparable,named "int8" "int8"
type t7 INT16 2 2 0 comparable,named "int16" "int16"
type t8 INT32 4 4 0 comparable,named "int32" "int32"
type t9 INT64 8 8 0 comparable,named "int64" "int64"
type t10 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t11 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t12 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t13 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t14 INT 8 8 0 comparable,named "int" "int"
type t15 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t16 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t17 UINT 8 8 0 comparable,named "uint" "uint"
type t18 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t8
type t21 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t12
type t22 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t14
type t23 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t18
type t24 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t15
type t25 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t16
type t26 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t19
type t27 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t28 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t29 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t30 SSA ? ? ? - "mem" ""
type t31 SSA ? ? ? - "flags" ""
type t32 SSA ? ? ? - "void" ""
type t33 SSA 16 8 ? - "int128" ""
type t34 RESULTS ? ? ? - "mem" "" 1 t30
type t35 PTR 8 8 8 hasptr,direct,comparable "**errorString" "**errors.errorString" t2
type t36 PTR 8 8 8 hasptr,direct,comparable "*string" "*string" t4
aux a5 str "" "" "go:string.\"\""
type t37 RESULTS ? ? ? - "string,mem" "" 2 t4,t30
slot s1 a3 t2 0 - 0
f b1 t1 a1 11 1
typs Bool=t5,Int8=t6,Int16=t7,Int32=t8,Int64=t9,UInt8=t10,UInt16=t11,UInt32=t12,UInt64=t13,Int=t14,Float32=t15,Float64=t16,UInt=t17,Uintptr=t18,String=t4,BytePtr=t19,Int32Ptr=t20,UInt32Ptr=t21,IntPtr=t22,UintptrPtr=t23,Float32Ptr=t24,Float64Ptr=t25,BytePtrPtr=t26,Complex64=t27,Complex128=t28,UnsafePtr=t29,Mem=t30,Flags=t31,Void=t32,Int128=t33,ResultMem=t34
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v7 ConstString t4 0 a5 p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p2:74:10:0:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4455667788=v7
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v7 ConstString t4 0 a5 p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4455667788=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:74:74
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v7 ConstString t4 0 a5 p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4455667788=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:74:74
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:74:74
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:74:74
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:74:74
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:74:74
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:74:74
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:74:74
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:74:74
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
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
cache linestarts 2:74:74
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
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
cache linestarts 2:74:74
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
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
cache linestarts 2:74:74
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
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
cache linestarts 2:74:74
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
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
cache linestarts 2:74:74
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
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
cache linestarts 2:74:74
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
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
cache linestarts 2:74:74
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
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
cache linestarts 2:74:74
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
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
cache linestarts 2:74:74
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 11 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p2:73:6:2:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 1 v9,v1
v v11 MakeResult t37 0 - p2:74:2:0:0 1 v10,v1
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
cache linestarts 2:74:74
dcllen 2
end
pass 20 "expand calls"
aux a6 nameoff "e+0" a3 0
type t38 RESULTS ? ? ? - "*uint8,int,mem" "" 3 t19,t14,t30
f b1 t1 a1 12 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v10 Load t4 0 - p2:74:10:0:0 2 v9,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v2,v12,v1
v v7 SB t18 0 - p0:0:0:0:0 0 -
v v5 SP t18 0 - p0:0:0:0:0 2 -
v v4 OffPtr t35 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t36 0 a4 p2:74:2:0:0 0 v5,v1
v v2 StringPtr t19 0 - p2:74:2:0:0 1 v10
v v12 StringLen t14 0 - p2:74:2:2:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 2 v8
v v10 StringMake t4 0 - p2:74:10:0:0 0 v13,v14
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v7 SB t18 0 - p0:0:0:0:0 0 -
v v5 SP t18 0 - p0:0:0:0:0 2 -
v v4 OffPtr t35 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t36 0 a4 p2:74:2:0:0 0 v5,v1
v v13 Load t19 0 - p2:74:10:0:0 2 v9,v1
v v14 Load t14 0 - p2:74:10:0:0 2 v15,v1
v v15 OffPtr t22 8 - p2:74:10:0:0 1 v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4
freev v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 2 v8
v v10 StringMake t4 0 - p2:74:10:0:0 0 v13,v14
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v7 SB t18 0 - p0:0:0:0:0 0 -
v v5 SP t18 0 - p0:0:0:0:0 2 -
v v4 OffPtr t35 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t36 0 a4 p2:74:2:0:0 0 v5,v1
v v13 Load t19 0 - p2:74:10:0:0 2 v9,v1
v v14 Load t14 0 - p2:74:10:0:0 2 v15,v1
v v15 OffPtr t22 8 - p2:74:10:0:0 1 v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4
freev v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 2 v8
v v10 StringMake t4 0 - p2:74:10:0:0 0 v13,v14
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v7 SB t18 0 - p0:0:0:0:0 0 -
v v5 SP t18 0 - p0:0:0:0:0 2 -
v v4 OffPtr t35 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t36 0 a4 p2:74:2:0:0 0 v5,v1
v v13 Load t19 0 - p2:74:10:0:0 2 v9,v1
v v14 Load t14 0 - p2:74:10:0:0 2 v15,v1
v v15 OffPtr t22 8 - p2:74:10:0:0 1 v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4
freev v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 2 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Load t19 0 - p2:74:10:0:0 1 v9,v1
v v14 Load t14 0 - p2:74:10:0:0 1 v15,v1
v v15 OffPtr t22 8 - p2:74:10:0:0 1 v8
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 2 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Load t19 0 - p2:74:10:0:0 1 v9,v1
v v14 Load t14 0 - p2:74:10:0:0 1 v15,v1
v v15 OffPtr t22 8 - p2:74:10:0:0 1 v8
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 2 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Load t19 0 - p2:74:10:0:0 1 v9,v1
v v14 Load t14 0 - p2:74:10:0:0 1 v15,v1
v v15 OffPtr t22 8 - p2:74:10:0:0 1 v8
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 2 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Load t19 0 - p2:74:10:0:0 1 v9,v1
v v14 Load t14 0 - p2:74:10:0:0 1 v15,v1
v v15 OffPtr t22 8 - p2:74:10:0:0 1 v8
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 2 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Load t19 0 - p2:74:10:0:0 1 v9,v1
v v14 Load t14 0 - p2:74:10:0:0 1 v15,v1
v v15 OffPtr t22 8 - p2:74:10:0:0 1 v8
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 2 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Load t19 0 - p2:74:10:0:0 1 v9,v1
v v14 Load t14 0 - p2:74:10:0:0 1 v15,v1
v v15 OffPtr t22 8 - p2:74:10:0:0 1 v8
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 2 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Load t19 0 - p2:74:10:0:0 1 v9,v1
v v14 Load t14 0 - p2:74:10:0:0 1 v15,v1
v v15 OffPtr t22 8 - p2:74:10:0:0 1 v8
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 2 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Load t19 0 - p2:74:10:0:0 1 v9,v1
v v14 Load t14 0 - p2:74:10:0:0 1 v15,v1
v v15 OffPtr t22 8 - p2:74:10:0:0 1 v8
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 NilCheck t2 0 - p2:74:10:1:0 2 v6,v1
v v9 OffPtr t36 0 - p2:74:10:0:0 1 v8
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Load t19 0 - p2:74:10:0:0 1 v9,v1
v v14 Load t14 0 - p2:74:10:0:0 1 v15,v1
v v15 OffPtr t22 8 - p2:74:10:0:0 1 v8
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 2 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 ARM64MOVDload t19 0 - p2:74:10:0:0 1 v8,v1
v v14 ARM64MOVDload t14 8 - p2:74:10:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v15,v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 2 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 ARM64MOVDload t19 0 - p2:74:10:0:0 1 v8,v1
v v14 ARM64MOVDload t14 8 - p2:74:10:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v15,v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 2 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 ARM64MOVDload t19 0 - p2:74:10:0:0 1 v8,v1
v v14 ARM64MOVDload t14 8 - p2:74:10:0:0 1 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v15,v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 36 "pair"
type t39 TUPLE ? ? ? - "*uint8,int" "" t19 t14
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:74:74
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p2:74:10:1:0 1 v6,v1
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v8 ARM64LoweredNilCheck t32 0 - p2:74:10:1:0 0 v6,v1
v v15 ARM64LDP t39 0 - p2:74:10:0:0 2 v6,v1
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v15 ARM64LDP t39 0 - p2:74:10:1:0 2 v6,v1
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v15 ARM64LDP t39 0 - p2:74:10:1:0 2 v6,v1
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v3,v4,v5,v7,v10,v12,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{errors.(*errorString).Error}" a2 1 1 1 8 8 1 2
abiparam in 0 t2 a3 0 0
abiparam out 0 t4 a4 0,1 -1
callreg 0:1,1:2 - 0 -
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v15 ARM64LDP t39 0 - p2:74:10:1:0 2 v6,v1
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v9,v10,v12
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
fstate scheduled,laidout
regalloc 16 v6:R0,v11:[],v13:R0,v14:R1,v15:(R0;R1)
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v15 ARM64LDP t39 0 - p2:74:10:1:0 2 v6,v1
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v9,v10,v12
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
fstate scheduled,laidout
regalloc 16 v6:R0,v11:[],v13:R0,v14:R1,v15:(R0;R1)
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 15 1
b b1 Ret p2:74:10:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a6 p2:74:10:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v15 ARM64LDP t39 0 - p2:74:10:1:0 2 v6,v1
v v14 Select1 t14 0 - p2:74:10:0:0 1 v15
v v13 Select0 t19 0 - p2:74:10:0:0 1 v15
v v11 MakeResult t38 0 - p2:74:2:0:0 1 v13,v14,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v9,v10,v12
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:74:74
fstate scheduled,laidout
regalloc 16 v6:R0,v11:[],v13:R0,v14:R1,v15:(R0;R1)
dcllen 2
end
frontend
end
ptrcache t3,t4,t7,t8,t9,t10,t12,t14,t15,t16,t18,t19,t26,t36
typelink t30=t34
typeorder t6,t10,t7,t11,t8,t12,t9,t13,t14,t17,t18,t27,t28,t15,t16,t5,t19,t20,t21,t22,t23,t24,t25,t26,t35,t2,t36,t1,t3,t4,t29,t30,t32,t31,t33,t39,t34,t37,t38
eof
"#

/-- `std/errors/(*errorString).Error,1.prog` (quick-v10). -/
def errProg : String := r#"gofv-prog 3
pkg "errors"
func "(*errorString).Error" 1
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
type t1 8 8 8 1 01 "*errorString"
name n1 "e" PPARAM t1 1 "errors.e" 0 a3
type t2 16 8 8 1 01 "string"
name n2 "~r0" PPARAMOUT t2 1 "errors.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p2 "errors/errors.go" 1 1 -1 1 "errors/errors.go" "errors/errors.go" 1 1
sym y1 "errors.(*errorString).Error" 1
curfn p2:73:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 73 200080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "errors.(*errorString).Error.arginfo1" 0
sym y5 "errors.(*errorString).Error.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:73:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:73:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:73:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:73:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:73:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:73:6:2:0
p 6 6 0 0 0 - LDP 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REGREG/8192/0/0/NONE/0/8193/-/- 0 0 p2:74:10:1:0
p 7 7 0 0 0 - RET 0 _ 0 - _ 0 0 p2:74:10:2:0
p 8 8 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 73 200080
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
dbgpc 1:11:7
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p2:73:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:73:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:73:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:73:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p2:73:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:73:6:2:0
p 6 0 0 0 245 - LDP 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REGREG/8192/0/0/NONE/7/8193/-/- 0 0 p2:74:10:1:0
p 7 4 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:74:10:2:0
fn y1 8 0 0 0 73 2000c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 16 0 000440a9c0035fd60000000000000000 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y3,_,_,_,y4,y5
usedfiles 1
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 040400 0
data y10 SRODATA 3 1 28000 020400 0
data y11 SRODATA 3 1 28000 040400 0
data y12 SRODATA 4 1 28000 96010400 0
data y13 SRODATA 3 1 28000 000400 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "go:info.*errors.errorString" 0
sym y19 "go:info.string" 0
sym y20 "type:string" 0
dwfn y14 y15 y16 - y17 "errors.(*errorString).Error" 1:73 1 0 1 15
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "*errors.errorString" 0 0 1 p2:73:7:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "string" 0 0 1 p2:73:31:0:0
var 0 0 "e" 5 1 0 0 0 8 y18 "errors/errors.go" 73 7 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y19 "errors/errors.go" 73 31 0 1 0 0 -
scope 0 0 - 0,1
data y14 SDWARFFCN 65 0 0 036572726f72732e282a6572726f72537472696e67292e4572726f72000010019c0200000049012d6500004900000000000000002e7e7230000149000000000000 5
reloc 0 0 R_USETYPE 0 y20
reloc 29 1 R_DWTXTADDR_U1 0 y1
reloc 44 4 R_DWARFSECREF 0 y18
reloc 48 4 R_DWARFSECREF 0 y15
reloc 59 4 R_DWARFSECREF 0 y19
data y15 SDWARFLOC 8 0 0 0100040004015000 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 24 0 0 0009020000000000000000040203c400140637020c000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded `(*errorString).Error` (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load errSsa errProg

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

/-- The PC table `checkG4` gives: the index of each value's first Prog and of the terminator's
(`v15` from the `PCDATA` at 5 through the `LDP` at 6). -/
def tab : PcTab := [(1, [5, 5, 5, 7, 7, 7, 7])]

/-- The class table `checkG4` gives: nothing known at the entry `b1`. -/
def kt : KTab := [(1, KMap.bot)]

/-- Block `b1`: the entry values `v6 = ArgIntReg` (`R0`) and `v1 = InitMem`; `v15 = LDP v6 v1`
(`(R0, R1)`), `v14 = Select1 v15` (`R1`), `v13 = Select0 v15` (`R0`), `v11 = MakeResult`; `Ret`. -/
def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, no frame, every symbol at `symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 0 0 ps.toList

/-- A frameless activation (`SP = 0x7fff0000`, `g = 0x9000`, `LR = 0x40`, `FP = 0`) with the
globals at their symbols and the PC table of `checkG4`. -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := 0x7fff0000, slot := fun _ => none, g := 0x9000, lr := 0x40, fp := 0,
    framed := false, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The memory: a global `s` of 16 zero bytes (the string header `e` points to). -/
def memS : Mem := { blocks := #[(.global "s", { data := Array.replicate 16 (.b 0) })] }

def ptrS : Ptr := ⟨.global "s", 0⟩

/-- The `runLoc` state after the entry values: `e` (a pointer to `s`) in `R0`, every other register
`poison`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := memS },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .ptr ptrS else .poison,
    flags := .poison, slots := [], mem := .mem memS }

/-- The machine before `v15`: `X0` the address of `s`, the activation's `g`, `FP`, `LR`, the
memory 0. -/
def m0 : MState :=
  { x := fun k => if k = 0 then GenG2.symA else if k = 28 then 0x9000 else if k = 29 then 0 else
      if k = 30 then 0x40 else 0,
    sp := 0x7fff0000, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := fun _ => 0 }

/-- What compiled evaluation checks on `(*errorString).Error`: `checkG4` accepts it with `tab` and
`kt` and `checkG3` does not; there is no home slot and no static call; `b1` holds `v15`, `v14`,
`v13` at 2, 3, 4 with their ops; `v15` loads through `v6`, `R0` holds a 64-bit value after the entry
values, the pair load reads valid bytes at both addresses, and `stepLoc` runs `v15`, `v14`, `v13`. -/
def errFacts : Bool :=
  (checkG4 lc ps bs g).toOption == some (tab, kt) && (checkG3 lc ps bs g).toOption.isNone &&
    (homeSlots lc).isEmpty && GenG2.noCalls lc && lc.ctx.f.blocks.toList.contains 1 &&
    (lc.ctx.f.block? 1).isSome && (lc.ctx.f.value? 15).isSome && (lc.ctx.f.value? 14).isSome &&
    (lc.ctx.f.value? 13).isSome && blk1.values[2]? == some 15 && blk1.values[3]? == some 14 &&
    blk1.values[4]? == some 13 && (val 15).op == .ARM64LDP && (val 14).op == .Select1 &&
    (val 13).op == .Select0 && (val 15).args[0]? == some 6 &&
    (kAt lc kt 1 blk1 2).get 0 == some 64 &&
    GenG1.okThen (s0.read lc 6) (fun x => (pairAddr lc.ctx (val 15) 8 x).any fun pq =>
      (memS.read pq.1 8).isSome && (memS.read pq.2 8).isSome) &&
    GenG1.okThen (stepLoc default lc s0 (val 15)) fun s1 =>
      GenG1.okThen (stepLoc default lc s1 (val 14)) fun s2 =>
        GenG1.okThen (stepLoc default lc s2 (val 13)) fun _ => true

/-- `checkG4` accepts `pallocSum.start` (`GenG3`) with G3's tables. -/
def startG4 : Bool :=
  (checkG4 GenG3.lc GenG3.ps GenG3.bs GenG3.g).toOption == some (GenG3.tab, GenG3.kt)

theorem g4_facts : (errFacts && startG4) = true := by
  native_decide

theorem g4Env (hc : checkG4 lc ps bs g = .ok (tab, kt)) (hsl : (homeSlots lc).isEmpty = true)
    (hnc : GenG2.noCalls lc = true) : G2Env lc g L ps 0 tab E where
  lcEq := rfl
  link := rfl
  pcOf := rfl
  retOut := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG4_spec hc
    intro p hp
    exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
  addr := GenG2.addrAgree
  glob := fun _ _ _ _ => rfl
  syms := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG4_spec hc
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

theorem memInjS : MemInj GenG2.ι memS (fun _ => 0) where
  nil := rfl
  mapped := by
    intro b al h
    simp [memS] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨GenG2.symA, rfl, fun _ => by decide, by decide⟩
  inj := by
    intro b al b' al' a a' h h' hne
    simp [memS] at h h'
    exact absurd (h.1.trans h'.1.symm) hne
  bytes := ⟨fun _ _ => False, by
    intro b al a h _
    simp [memS] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun o ho => ho.elim, fun o _ ho => ho.elim, fun i hi _ => ?_⟩
    simp [ByteRel]⟩

theorem keysS : KeysNodup memS := by simp [KeysNodup, memS]

theorem sepS : SepFrom GenG2.ι (StkAt E) memS := by
  intro b al a _ _ y hy
  rcases hy with ⟨h1, -⟩ | ⟨k, off, h, -⟩
  · cases h1
  · cases h

theorem locMatch0 : LocMatch E s0 1 2 m0 where
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
          exact ⟨GenG2.symA, rfl, by decide⟩
        · subst hv; trivial
      · split at hv
        · rename_i h0; subst h0; simp [objV?] at hk
        · subst hv; trivial
    · cases hv
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨memS, rfl, memInjS⟩
  frame := ⟨rfl, rfl, (fun h => by cases h), fun _ => ⟨rfl, rfl⟩⟩
  pc := rfl

theorem g4Inv0 {K : KMap} (h0 : K.get 0 = some 64) : G3Inv E lc K s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, memS, rfl, keysS, sepS⟩
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

/-- The per-value premises of a value that is no compare, load or pair load. -/
theorem g4Pre_of {v : Value} (h1 : v.op ≠ .ARM64CMP) (h2 : v.op ≠ .ARM64CMPconst)
    (h3 : loadOp? v.op = none) (h4 : v.op ≠ .ARM64LDP) (s : LocState) : G4Pre lc s v :=
  ⟨⟨fun h => by rcases h with h | h <;> contradiction, fun _ _ _ hl => by rw [h3] at hl; cases hl⟩,
    fun h => absurd h h4⟩

/-- **G4 on `(*errorString).Error`**: from the state after the entry values (`e` in `R0`), the
pair load `v15` (`LDP (R0), (R0, R1)`) and its components `v14` (`R1`) and `v13` (`R0`) are matched
by a machine run of the Progs to a state related before `v11`, with the registers at their
classes, under an activation that extends `E`. -/
theorem genG4_value_witness :
    ∃ s1 s2 s3 E' m3, stepLoc default lc s0 (val 15) = .ok s1 ∧
      stepLoc default lc s1 (val 14) = .ok s2 ∧ stepLoc default lc s2 (val 13) = .ok s3 ∧
      E.Extends E' ∧ G2Env lc g L ps 0 tab E' ∧ PStar GenG2.H0 L ps.toList 0 m0 m3 ∧
      LocMatch E' s3 1 5 m3 ∧ G3Inv E' lc (kAt lc kt 1 blk1 5) s3 := by
  have h := g4_facts
  simp only [Bool.and_eq_true] at h
  have hf := h.1
  simp only [errFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hsl⟩, hnc⟩, hm1⟩, hb1s⟩, hv15s⟩, hv14s⟩, hv13s⟩, hi2⟩,
    hi3⟩, hi4⟩, hop15⟩, hop14⟩, hop13⟩, harg⟩, hk0⟩, hpair⟩, hrun⟩ := hf
  have hc : checkG4 lc ps bs g = .ok (tab, kt) := by
    revert hres; cases checkG4 lc ps bs g <;> simp [Except.toOption]
  have hb : lc.ctx.f.block? 1 = some blk1 := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [blk1, hb]
  have hval : ∀ n, (lc.ctx.f.value? n).isSome = true → lc.ctx.f.value? n = some (val n) := by
    intro n h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    simp [val, hv]
  have hE := g4Env hc hsl hnc
  obtain ⟨s1, hs1, hrun⟩ := GenG1.okThen_spec hrun
  obtain ⟨s2, hs2, hrun⟩ := GenG1.okThen_spec hrun
  obtain ⟨s3, hs3, -⟩ := GenG1.okThen_spec hrun
  obtain ⟨x0, hx0, hpq⟩ := GenG1.okThen_spec hpair
  have hpre15 : G4Pre lc s0 (val 15) := by
    refine ⟨⟨fun h => (by rcases h with h | h <;> rw [hop15] at h <;> cases h),
      fun _ _ _ hl => (by rw [hop15] at hl; simp [loadOp?, narrowLoad?] at hl)⟩,
      fun _ a x ha hx => ?_⟩
    rw [harg] at ha
    cases ha
    rw [hx0] at hx
    cases hx
    obtain ⟨⟨p, q⟩, hpq', hr⟩ := (Option.any_eq_true _ _).1 hpq
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hr
    obtain ⟨⟨bs1, hbs1⟩, ⟨bs2, hbs2⟩⟩ := hr
    exact ⟨p, q, memS, bs1, bs2, hpq', rfl, hbs1, hbs2⟩
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', hinv1⟩ := g4_value (H := GenG2.H0) hc hE hm1 hb hi2
    (hval 15 hv15s) (by rw [hop15]; rfl) locMatch0 (g4Inv0 hk0) hpre15
    (GenG2.callOK_ne (by rw [hop15]; decide)) hs1
  obtain ⟨E2, m2, hx2, hE2, hp2, hm2', hinv2⟩ := g4_value (H := GenG2.H0) hc hE1 hm1 hb hi3
    (hval 14 hv14s) (by rw [hop14]; rfl) hm1' hinv1
    (g4Pre_of (by rw [hop14]; decide) (by rw [hop14]; decide)
      (by rw [hop14]; simp [loadOp?, narrowLoad?]) (by rw [hop14]; decide) _)
    (GenG2.callOK_ne (by rw [hop14]; decide)) hs2
  obtain ⟨E3, m3, hx3, hE3, hp3, hm3', hinv3⟩ := g4_value (H := GenG2.H0) hc hE2 hm1 hb hi4
    (hval 13 hv13s) (by rw [hop13]; rfl) hm2' hinv2
    (g4Pre_of (by rw [hop13]; decide) (by rw [hop13]; decide)
      (by rw [hop13]; simp [loadOp?, narrowLoad?]) (by rw [hop13]; decide) _)
    (GenG2.callOK_ne (by rw [hop13]; decide)) hs3
  exact ⟨s1, s2, s3, E3, m3, hs1, hs2, hs3,
    MatchEnv.Extends.trans (MatchEnv.Extends.trans hx1 hx2) hx3, hE3,
    (hp1.trans hp2).trans hp3, hm3', hinv3⟩

/-- **G4 on `pallocSum.start`**: `g4_term` on the bit test `TBNZ [63]` (bit 63 of `x = 7` clear)
gives a machine run to a state related before the first value of `b2`, with the registers at its
classes. -/
theorem genG4_term_witness :
    ∃ s1 e m1, stepTermLoc GenG3.lc (GenG2.s0 7) GenG3.blk1 = .ok (.goto e, s1) ∧ e.b = 2 ∧
      PStar GenG2.H0 GenG3.L GenG3.ps.toList 0 (GenG3.m0 7) m1 ∧ LocMatch GenG3.E s1 2 0 m1 ∧
      G3Inv GenG3.E GenG3.lc (GenG3.kt.at 2) s1 := by
  have h := g4_facts
  simp only [Bool.and_eq_true] at h
  have hc4 : checkG4 GenG3.lc GenG3.ps GenG3.bs GenG3.g = .ok (GenG3.tab, GenG3.kt) := by
    have h2 := h.2
    simp only [startG4, beq_iff_eq] at h2
    revert h2; cases checkG4 GenG3.lc GenG3.ps GenG3.bs GenG3.g <;> simp [Except.toOption]
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
  have hE := GenG3.g3Env hc3 hsl hnc
  obtain ⟨⟨n, s1⟩, hs1, hrun⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨hgo, -⟩ := hrun
  obtain ⟨e, rfl, het⟩ := GenG1.gotoIs_spec hgo
  obtain ⟨m1, hp1, hlm1, hinv1, -⟩ := g4_term (H := GenG2.H0) hc4 hE hm1 hb1
    (GenG3.locMatch0 7) (GenG3.g3Inv0 7 (by rw [hsz]; exact hk0))
    (fun hz => by rw [hkind] at hz; rcases hz with h | h <;> cases h) hs1
  exact ⟨s1, e, m1, hs1, het, hp1, het ▸ hlm1, het ▸ hinv1⟩

end GoFV.Proof.Witness.GenG4
