import GoFV.Proof.Gen.G19
import GoFV.Proof.Witness.GenG18

/-!
# Non-vacuity witness: slice G19 of the genssa validator on `main.func1` (`test/convert4`)

`test/convert4/main/main.func1,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`): the closure
`func() { _ = [9]byte(s) }` of `test/convert4.go` (line 37), `s` a captured `[]byte`.

`checkG18` rejects it (`v11 = LoweredPanicBoundsCR`); `checkG19` accepts it with the PC table `tab`
and the class table `kt`. Block `b3` (the `Exit` block): `v11 = LoweredPanicBoundsCR [16] {9} v3`,
the conversion's bounds panic (`BoundsConvert`, kind 16) of the constant length 9 and `len(s)` in
`R0`. Its Progs: `PCDATA $1, $0`, `PCDATA $PCDATA_PanicBounds, $350` (`abi.BoundsEncode` of code 8,
unsigned, the constant 9 and `R0`), `CALL runtime.panicBounds(SB)`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g19_facts`),
`stepLoc` runs `v11` from a state with `len(s) = 5` in `R0` to the panic `.bounds 16 9 5`, and the
only `CALL` of `runtime.panicBounds` has the `PCDATA_PanicBounds` value 350 in force. The hook `H`
panics with `boundsPanic 350`, so it meets `BoundsOK`. On a framed activation with `G10Env` (as
`GenG18`'s), `g19_boundsPanic` runs the `PCDATA`s and the `CALL` from the machine with `X0 = 5`
and the machine panics with the same `.bounds 16 9 5` (`genG19_boundsPanic_witness`).
-/

namespace GoFV.Proof.Witness.GenG19

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/convert4/main/main.func1,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "main.func1" 1 0 0
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
type t1 FUNC 8 8 8 hasptr,direct "func()" "func()" 0 0 0
aux a2 sym "main.main.func1" "main.main.func1" 1 - 0 - - - - 0
aux a1 call "AuxCall{main.main.func1}" a2 1 0 0 8 0 0 0
type t2 BOOL 1 1 0 comparable,named "bool" "bool"
type t3 INT8 1 1 0 comparable,named "int8" "int8"
type t4 INT16 2 2 0 comparable,named "int16" "int16"
type t5 INT32 4 4 0 comparable,named "int32" "int32"
type t6 INT64 8 8 0 comparable,named "int64" "int64"
type t7 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t8 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t9 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t10 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t11 INT 8 8 0 comparable,named "int" "int"
type t12 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t13 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t7
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t5
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t9
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t11
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
posbase p2 "./convert4.go" 1 1 -1
type t35 UINT8 1 1 0 comparable,named "byte" "uint8"
type t34 SLICE 24 8 8 hasptr "[]byte" "[]uint8" t35
type t33 PTR 8 8 8 hasptr,direct,comparable "*[]byte" "*[]uint8" t34
type t37 ARRAY 9 1 0 comparable "[9]byte" "[9]uint8" t35 9
type t36 PTR 8 8 8 hasptr,direct,comparable "*[9]byte" "*[9]uint8" t37
aux a3 name "s" "s" PAUTO t34 0 0 used p2:37:19:0:0
slot s1 a3 t34 0 - 0
f b1 t1 a1 14 3
typs Bool=t2,Int8=t3,Int16=t4,Int32=t5,Int64=t6,UInt8=t7,UInt16=t8,UInt32=t9,UInt64=t10,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 0 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:0:0 2 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:0:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v12 SlicePtr t36 0 - p2:37:19:0:0 0 v6
v v13 Copy t28 0 - p2:38:3:2:0 1 v1
v v14 MakeResult t32 0 - p2:38:3:0:0 1 v13
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v10 Copy t28 0 - p2:37:19:2:0 1 v1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v10
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev -
freeb -
dcllen 1
end
pass 1 "number lines"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 0 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 2 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v12 SlicePtr t36 0 - p2:37:19:0:0 0 v6
v v13 Copy t28 0 - p2:38:3:2:0 1 v1
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v13
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v10 Copy t28 0 - p2:37:19:2:0 1 v1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v10
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev -
freeb -
cache postorder b2,b3,b1
cache linestarts 2:36:38
dcllen 1
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 0 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 2 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v12 SlicePtr t36 0 - p2:37:19:0:0 0 v6
v v13 Copy t28 0 - p2:38:3:2:0 0 v1
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v10 Copy t28 0 - p2:37:19:2:0 0 v1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev -
freeb -
cache postorder b2,b3,b1
cache linestarts 2:36:38
dcllen 1
end
pass 3 "early deadcode"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:36:38
dcllen 1
end
pass 4 "short circuit"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:36:38
dcllen 1
end
pass 5 "decompose user"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:36:38
dcllen 1
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:36:38
dcllen 1
end
pass 7 "opt"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:36:38
dcllen 1
end
pass 8 "zero arg cse"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:36:38
dcllen 1
end
pass 9 "opt deadcode"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache linestarts 2:36:38
dcllen 1
end
pass 10 "generic cse"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 1
end
pass 11 "phiopt"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 1
end
pass 12 "gcse deadcode"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 1
end
pass 13 "nilcheckelim"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 1
end
pass 14 "prove"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 1
end
pass 15 "divisible"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 1
end
pass 16 "divmod"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 1
end
pass 17 "middle opt"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 1
end
pass 18 "known bits"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 1
end
pass 19 "early fuse"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v10,v13,v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 1
end
pass 20 "expand calls"
f b1 t1 a1 14 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:36:3:0:0 1 v4
v v6 Load t34 0 - p2:36:3:1:0 1 v5,v1
v v8 SliceLen t11 0 - p2:37:19:1:0 2 v6
v v9 IsSliceInBounds t2 0 - p2:37:19:0:0 1 v7,v8
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v13 SP t15 0 - p0:0:0:0:0 0 -
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v8,v1
names s1
named s1 v6
splits -
canon a3/t34/0/-/0=s1
consts 9=v7
freev v12,v3,v2
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 1
end
pass 21 "decompose builtin"
type t38 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t35
aux a4 name "s.ptr" "s.ptr" PAUTO t38 0 3 used p2:37:19:0:0
slot s2 a4 t38 0 s1 0
aux a5 name "s.len" "s.len" PAUTO t11 0 3 used p2:37:19:0:0
slot s3 a5 t11 0 s1 8
aux a6 name "s.cap" "s.cap" PAUTO t11 0 3 used p2:37:19:0:0
slot s4 a6 t11 0 s1 16
f b1 t1 a1 16 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:36:3:0:0 3 v4
v v6 SliceMake t34 0 - p2:36:3:1:0 0 v12,v3,v15
v v9 IsSliceInBounds t2 0 - p2:37:19:1:0 1 v7,v3
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v13 SP t15 0 - p0:0:0:0:0 0 -
v v12 Load t38 0 - p2:36:3:1:0 1 v5,v1
v v3 Load t11 0 - p2:36:3:1:0 3 v2,v1
v v2 OffPtr t20 8 - p2:36:3:1:0 1 v5
v v15 Load t11 0 - p2:36:3:1:0 1 v16,v1
v v16 OffPtr t20 16 - p2:36:3:1:0 1 v5
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v3,v1
names s2,s3,s4
named s2 v12
named s3 v3
named s4 v15
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts 9=v7
freev v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 22 "softfloat"
f b1 t1 a1 16 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:36:3:0:0 3 v4
v v6 SliceMake t34 0 - p2:36:3:1:0 0 v12,v3,v15
v v9 IsSliceInBounds t2 0 - p2:37:19:1:0 1 v7,v3
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v13 SP t15 0 - p0:0:0:0:0 0 -
v v12 Load t38 0 - p2:36:3:1:0 1 v5,v1
v v3 Load t11 0 - p2:36:3:1:0 3 v2,v1
v v2 OffPtr t20 8 - p2:36:3:1:0 1 v5
v v15 Load t11 0 - p2:36:3:1:0 1 v16,v1
v v16 OffPtr t20 16 - p2:36:3:1:0 1 v5
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v3,v1
names s2,s3,s4
named s2 v12
named s3 v3
named s4 v15
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts 9=v7
freev v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 23 "branchelim"
f b1 t1 a1 16 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:36:3:0:0 3 v4
v v6 SliceMake t34 0 - p2:36:3:1:0 0 v12,v3,v15
v v9 IsSliceInBounds t2 0 - p2:37:19:1:0 1 v7,v3
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v13 SP t15 0 - p0:0:0:0:0 0 -
v v12 Load t38 0 - p2:36:3:1:0 1 v5,v1
v v3 Load t11 0 - p2:36:3:1:0 3 v2,v1
v v2 OffPtr t20 8 - p2:36:3:1:0 1 v5
v v15 Load t11 0 - p2:36:3:1:0 1 v16,v1
v v16 OffPtr t20 16 - p2:36:3:1:0 1 v5
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v3,v1
names s2,s3,s4
named s2 v12
named s3 v3
named s4 v15
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts 9=v7
freev v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 24 "late opt"
f b1 t1 a1 16 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v9 IsSliceInBounds t2 0 - p2:37:19:1:0 1 v7,v3
v v3 Load t11 0 - p2:36:3:1:0 2 v2,v1
v v2 OffPtr t20 16 - p2:36:3:2:0 1 v4
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v3,v1
names s2,s3,s4
named s2 v12
named s3 v3
named s4 v15
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts 9=v7
freev v16,v15,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38:36=1
dcllen 4
end
pass 25 "dead auto elim"
f b1 t1 a1 16 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v9 IsSliceInBounds t2 0 - p2:37:19:1:0 1 v7,v3
v v3 Load t11 0 - p2:36:3:1:0 2 v2,v1
v v2 OffPtr t20 16 - p2:36:3:2:0 1 v4
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v3,v1
names s2,s3,s4
named s2 v12
named s3 v3
named s4 v15
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts 9=v7
freev v16,v15,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38:36=1
dcllen 4
end
pass 26 "sccp"
f b1 t1 a1 16 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v9 IsSliceInBounds t2 0 - p2:37:19:1:0 1 v7,v3
v v3 Load t11 0 - p2:36:3:1:0 2 v2,v1
v v2 OffPtr t20 16 - p2:36:3:2:0 1 v4
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v3,v1
names s2,s3,s4
named s2 v12
named s3 v3
named s4 v15
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts 9=v7
freev v16,v15,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38:36=1
dcllen 4
end
pass 27 "generic deadcode"
f b1 t1 a1 16 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v9 IsSliceInBounds t2 0 - p2:37:19:1:0 1 v7,v3
v v3 Load t11 0 - p2:36:3:1:0 2 v2,v1
v v2 OffPtr t20 16 - p2:36:3:2:0 1 v4
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts 9=v7
freev v16,v15,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 28 "late fuse"
f b1 t1 a1 16 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v9 IsSliceInBounds t2 0 - p2:37:19:1:0 1 v7,v3
v v3 Load t11 0 - p2:36:3:1:0 2 v2,v1
v v2 OffPtr t20 16 - p2:36:3:2:0 1 v4
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts 9=v7
freev v16,v15,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 29 "check bce"
f b1 t1 a1 16 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v9 IsSliceInBounds t2 0 - p2:37:19:1:0 1 v7,v3
v v3 Load t11 0 - p2:36:3:1:0 2 v2,v1
v v2 OffPtr t20 16 - p2:36:3:2:0 1 v4
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts 9=v7
freev v16,v15,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 30 "dse"
f b1 t1 a1 16 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v9 IsSliceInBounds t2 0 - p2:37:19:1:0 1 v7,v3
v v3 Load t11 0 - p2:36:3:1:0 2 v2,v1
v v2 OffPtr t20 16 - p2:36:3:2:0 1 v4
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts 9=v7
freev v16,v15,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 31 "memcombine"
f b1 t1 a1 16 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v9 IsSliceInBounds t2 0 - p2:37:19:1:0 1 v7,v3
v v3 Load t11 0 - p2:36:3:1:0 2 v2,v1
v v2 OffPtr t20 16 - p2:36:3:2:0 1 v4
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts 9=v7
freev v16,v15,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 32 "writebarrier"
f b1 t1 a1 16 3
b b1 If p2:37:19:0:0 1 0 - v9 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v7 Const64 t11 9 - p0:0:0:0:0 2 -
v v9 IsSliceInBounds t2 0 - p2:37:19:1:0 1 v7,v3
v v3 Load t11 0 - p2:36:3:1:0 2 v2,v1
v v2 OffPtr t20 16 - p2:36:3:2:0 1 v4
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 PanicBounds t28 16 - p2:37:19:0:0 1 v7,v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts 9=v7
freev v16,v15,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 33 "lower"
aux a7 pbc "{9}" 9
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 34 "addressing modes"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 35 "late lower"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 36 "pair"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 38 "lowered cse"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 39 "elim unread autos"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 41 "lowered deadcode"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 42 "checkLower"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 43 "loop invariant"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 45 "tighten"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 46 "late deadcode"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 47 "critical"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 48 "phi tighten"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 49 "likelyadjust"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap -:1
cache linestarts 2:36:38
dcllen 4
end
pass 50 "layout"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap -:1
cache linestarts 2:36:38
fstate laidout
dcllen 4
end
pass 51 "schedule"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap -:1
cache linestarts 2:36:38
fstate scheduled,laidout
dcllen 4
end
pass 52 "late nilcheck"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap -:1
cache linestarts 2:36:38
fstate scheduled,laidout
dcllen 4
end
pass 53 "flagalloc"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v16,v2,v9,v7,v12,v13,v10,v6,v5,v8
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap -:1
cache linestarts 2:36:38
fstate scheduled,laidout
dcllen 4
end
pass 54 "regalloc"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v2,v5,v6,v7,v8,v9,v10,v12,v13,v16
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap -:1
cache linestarts 2:36:38
fstate scheduled,laidout
regalloc 5 v3:R0,v4:R26
dcllen 4
end
pass 55 "loop rotate"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v2,v5,v6,v7,v8,v9,v10,v12,v13,v16
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap -:1
cache linestarts 2:36:38
fstate scheduled,laidout
regalloc 5 v3:R0,v4:R26
dcllen 4
end
pass 56 "trim"
f b1 t1 a1 16 3
b b1 ARM64UGE p2:37:19:0:0 1 0 - v15 b2:0,b3:0 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 ARM64MOVDload t11 16 - p2:36:3:1:0 2 v4,v1
v v15 ARM64CMPconst t29 9 - p2:37:19:1:0 1 v3
b b2 Ret p2:38:3:0:0 0 0 - v14 - b1:0
v v14 MakeResult t32 0 - p2:38:3:1:0 1 v1
b b3 Exit p2:37:19:0:0 0 0 - v11 - b1:1
v v11 ARM64LoweredPanicBoundsCR t28 16 a7 p2:37:19:0:0 1 v3,v1
names s3
named s3 v3
splits s1/0/t38=s2,s1/8/t11=s3,s1/16/t11=s4
canon a3/t34/0/-/0=s1
consts -
freev v2,v5,v6,v7,v8,v9,v10,v12,v13,v16
freeb -
cache postorder b2,b3,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b2:b1:-:-:11:14,b3:b1:-:b2:5:8
cache loopnest 4 0 - -
cache auxmap -:1
cache linestarts 2:36:38
fstate scheduled,laidout
regalloc 5 v3:R0,v4:R26
dcllen 4
end
frontend
end
ptrcache t4,t5,t6,t7,t9,t11,t12,t13,t15,t16,t17,t24,t34,t35,t37,t38
typelink t7=t35,t17=t38,t28=t32
typeorder t3,t7=t35,t4,t8,t5,t9,t6,t10,t11,t14,t15,t25,t26,t12,t13,t2,t17=t38,t18,t19,t20,t21,t22,t23,t24,t33,t36,t1,t34,t37,t16,t27,t28,t30,t29,t31,t32
eof
"#

/-- `test/convert4/main/main.func1,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "main.func1" 1
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
type t1 24 8 8 1 01 "[]byte"
name n1 "s" PAUTO t1 0 "main.s" 0 a3
type t2 8 8 8 1 01 "*byte"
name n2 "s.ptr" PAUTO t2 3 "main.s.ptr" 0 a4
type t3 8 8 0 0 - "int"
name n3 "s.len" PAUTO t3 3 "main.s.len" 0 a5
name n4 "s.cap" PAUTO t3 3 "main.s.cap" 0 a6
in n1 0 used
in n2 0 used
in n3 0 used
in n4 0 used
opt n1 0 -
opt n2 0 -
opt n4 0 -
opt n3 0 -
stack 0 0 8
end
genin
posbase p2 "./convert4.go" 1 1 -1 1 "./convert4.go" "./convert4.go" 1 1
sym y1 "main.main.func1" 1
curfn p2:36:3:0:0 0 0
regargs -
text y1 0 0 0 0 36 2080a0
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.panicBounds" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i0 0 0 p2:36:3:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:36:3:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:36:3:0:0
p 3 3 0 0 0 - MOVD 0 MEM/8218/0/0/NONE/0/16/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:36:3:2:0
p 4 4 0 0 0 - CMP 0 CONST/0/0/0/NONE/0/9/-/- 8192 - _ 0 0 p2:37:19:1:0
p 5 5 0 0 0 - BLO 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@7 0 0 p2:37:19:2:0
p 6 6 0 0 0 - RET 0 _ 0 - _ 0 0 p2:38:3:0:0
p 7 7 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p2:37:19:2:0
p 8 8 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/4/-/- 0 - CONST/0/0/0/NONE/0/350/-/- 0 0 p2:37:19:2:0
p 9 9 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:37:19:2:0
p 10 10 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p2:37:19:0:0
p 11 11 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 36 2080a0
funcaux y2 y2 - - - - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4
autot -
dbgentry 1
dbgslot 0 n3 t3 0
dbgvar 0 n1 0
dbgloc 0 1:3:-1:-30000:50
dbgregout -
dbgpc 1:3:4
end
asm
sym y4 "runtime.morestack" 0
sym y5 "" 0
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i0 0 0 p2:36:3:0:0
p 12 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:36:3:0:0
p 13 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:36:3:0:0
p 14 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:36:3:0:0
p 15 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@24 0 0 p2:36:3:0:0
p 16 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:36:3:0:0
p 17 12 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p2:36:3:0:1
p 18 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:36:3:0:0
p 19 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:36:3:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:36:3:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:36:3:0:0
p 3 24 0 0 333 - MOVD 0 MEM/8218/0/0/NONE/86/16/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:36:3:2:0
p 4 28 0 0 96 - CMP 0 CONST/0/0/0/NONE/18/9/-/- 8192 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:37:19:1:0
p 5 32 0 0 80 - BLO 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/7/-/@7 0 0 p2:37:19:2:0
p 6 36 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:38:3:0:0
p 20 40 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:38:3:0:0
p 21 44 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:38:3:0:0
p 7 48 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p2:37:19:2:0
p 8 48 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/4/-/- 0 - CONST/0/0/0/NONE/18/350/-/- 0 0 p2:37:19:2:0
p 9 48 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y3/- 0 0 p2:37:19:2:0
p 10 52 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:37:19:0:0
p 22 56 -16 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:37:19:0:0
p 23 56 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:36:3:0:0
p 24 56 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:36:3:0:0
p 25 56 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:36:3:0:0
p 26 60 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y4/- 0 0 p2:36:3:0:0
p 27 64 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:36:3:0:0
p 28 64 16 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@12 0 0 p2:36:3:0:0
fn y1 0 8 0 0 36 2080a0
funcaux y2 y2 - - - - -
text 80 0 900b40f9ff6330eb89010054fe0f1ff8fd831ff8fd2300d1400b40f91f2400f183000054fd835ff8fe0741f8c0035fd6000000941f2003d5e3031eaa00000094f0ffff17000000000000000000000000 2
reloc 48 4 R_CALLARM64 0 y3
reloc 60 4 R_CALLARM64 0 y4
pcln y10 y11 y12 y13 y5,y6,y7,y8,y9 y2,y2
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y5 SRODATA 11 1 28000 00010102020b0102020400 0
data y6 SRODATA 7 1 28000 000c0202010600 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 6 1 28000 000cbe050800 0
data y10 SRODATA 11 1 28000 020420071f0120021f0600 0
data y11 SRODATA 3 1 28000 041400 0
data y12 SRODATA 11 1 28000 4a07020202030102010600 0
data y13 SRODATA 3 1 28000 001400 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "go:info.[]uint8" 0
dwfn y14 y15 y16 - y17 "main.main.func1" 1:36 1 0 1 11
dwdcl -
dwclosure 1 n1:8
dwparents -
dwparams -
dwname n1 1 0 0 0 0 0 0 0 - p2:25:2:0:0 "[]uint8" 0 0 1 p2:37:19:0:0
dwname n2 1 0 0 0 0 0 0 0 - - "*uint8" 0 0 1 p2:37:19:0:0
dwname n4 1 0 0 0 0 0 0 0 - - "int" 0 0 1 p2:37:19:0:0
dwname n3 1 0 0 0 0 0 0 0 - - "int" 0 0 1 p2:37:19:0:0
var 0 0 "s" 52 1 0 0 0 -8 y18 "./convert4.go" 37 19 0 0 0 8 v0
scope 0 0 - 0
data y14 SDWARFFCN 41 0 0 036d61696e2e6d61696e2e66756e6331000050019c0200000024012573002500000000080000000000 3
reloc 17 1 R_DWTXTADDR_U1 0 y1
reloc 31 4 R_DWARFSECREF 0 y18
reloc 36 4 R_DWARFSECREF 0 y15
data y15 SDWARFLOC 8 0 0 0100041c50015000 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 36 0 0 00090200000000000000000402031e140a87068706380637063806860637360218000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded `main.func1` (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG19` gives (`b1`: `v3`'s `MOVD`, `v15`'s `CMP`, then `BLO`; `b2`: `RET`;
`b3`: `v11`'s `PCDATA`s and `CALL`, then the `HINT` after it). -/
def tab : PcTab := [(1, [3, 3, 3, 4, 5]), (2, [6, 6]), (3, [7, 10])]

/-- The class table `checkG19` gives (`R0` of class 64 in `b3`). -/
def kt : KTab := (match checkG19 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk3 : Block := (lc.ctx.f.block? 3).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG19`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The runtime: every call panics as `panicBounds64` with the `PCDATA_PanicBounds` value 350. -/
def H : Hooks := ⟨fun m => some (.panicked (boundsPanic 350 m) m)⟩

/-- The `runLoc` state before `v11`: `len(s) = 5` in `R0`, every other register `poison`, the empty
memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .i64 5 else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v11`: `X0 = 5`, the activation's `g` and `FP`, the PC of `v11`, the memory
0. -/
def m0 : MState :=
  { x := fun k => if k = 0 then 5 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 3 0, mem := fun _ => 0 }

/-- The result is the panic `.bounds 16 9 5`. -/
def isPanic (r : Res LocState) : Bool :=
  match r with
  | .panic e _ => decide (e = .bounds 16 9 5)
  | _ => false

theorem isPanic_spec {r : Res LocState} (h : isPanic r = true) :
    ∃ mm, r = .panic (.bounds 16 9 5) mm := by
  unfold isPanic at h
  split at h
  · rename_i e mm
    exact ⟨mm, by rw [of_decide_eq_true h]⟩
  · cases h

/-- Every `CALL` of `runtime.panicBounds` in `ps` has the `PCDATA_PanicBounds` value 350 in
force. -/
def pbAllOf (ps : List GoFV.Asm.Prog) (g : G2In) : Bool :=
  (List.range ps.length).all fun k =>
    match (ps[k]?).bind (·.to.sym) with
    | some y => g.syms[y]? != some pbSym || pbData ps k == some (constA 350)
    | none => true

def pbAll : Bool := pbAllOf ps.toList g

/-- What compiled evaluation checks on `main.func1`: `checkG19` accepts it with `tab` and `kt` and
`checkG18` does not; it accesses no frame variable and has no home slot; `b3` holds `v11` at index
0, a bounds panic, and `R0` has class 64 before it; `stepLoc` runs `v11` from `s0` to the panic
`.bounds 16 9 5`; and `pbAll`. -/
def gFacts : Bool :=
  (checkG19 lc ps bs g).toOption == some (tab, kt) && (checkG18 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 3 && (lc.ctx.f.block? 3).isSome &&
    (lc.ctx.f.value? 11).isSome && blk3.values[0]? == some 11 &&
    pbOp (val 11).op && (kAt lc kt 3 blk3 0).get 0 == some 64 &&
    isPanic (stepLoc GenG2.env lc s0 (val 11)) && pbAll

theorem g19_facts : gFacts = true := by
  native_decide

/-- The facts of `g19_facts` as hypotheses. -/
theorem facts :
    checkG19 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 3 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 3 = some blk3 ∧ lc.ctx.f.value? 11 = some (val 11) ∧
      blk3.values[0]? = some 11 ∧ pbOp (val 11).op = true ∧
      (kAt lc kt 3 blk3 0).get 0 = some 64 ∧
      isPanic (stepLoc GenG2.env lc s0 (val 11)) = true ∧ pbAll = true := by
  have hf := g19_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hm3⟩, hb3s⟩, hv11⟩, hi0⟩, hop⟩, hk0⟩, hrun⟩, hall⟩ := hf
  refine ⟨?_, hav, hsl, hm3, ?_, ?_, hi0, hop, hk0, hrun, hall⟩
  · revert hres; cases checkG19 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb3s
    simp [blk3, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv11
    simp [val, hv]

/-- `H` meets the hook contract when the only `PCDATA_PanicBounds` value at a `CALL` of
`runtime.panicBounds` is 350 (`pbAllOf`). -/
theorem boundsOK_of {ps : List GoFV.Asm.Prog} {g : G2In} {L : Link} (hall : pbAllOf ps g = true) :
    BoundsOK H g L ps := by
  intro k hk y c next m₁ hy hsym hdata _ _ _
  simp only [pbAllOf, List.all_eq_true, List.mem_range] at hall
  have h := hall k hk
  rw [List.getElem?_eq_getElem hk] at h
  simp only [Option.bind_some, hy, hsym, bne_self_eq_false, Bool.false_or, beq_iff_eq,
    hdata, Option.some.injEq] at h
  have hc : (c : Int) = 350 := by
    have := congrArg GoFV.Asm.Addr.offset h
    simpa [constA] using this
  have hc' : c = 350 := by omega
  subst hc'
  exact ⟨m₁, rfl⟩

/-- `H` meets the hook contract on `main.func1`. -/
theorem boundsOK (hall : pbAll = true) : BoundsOK H g L ps.toList := boundsOK_of hall

theorem g19Env (hc : checkG19 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -⟩ := checkG19_spec hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := GenG12.addrAgree
        glob := fun _ _ _ _ => rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -⟩ := checkG19_spec hc
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

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .i64 5) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 3 0 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl rfl
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g19Inv0 (h0 : (kAt lc kt 3 blk3 0).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 3 blk3 0) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, GenG2.keys0, GenG2.sep0⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- **G19 on `main.func1`**: from the state before `v11` with `len(s) = 5` in `R0`, `stepLoc` panics
with `.bounds 16 9 5` (converting a slice of length 5 to `[9]byte`), and `g19_boundsPanic` runs
`PCDATA $PCDATA_PanicBounds, $350` and `CALL runtime.panicBounds(SB)` from the machine with
`X0 = 5` to a state where `runProg` panics with the same `.bounds 16 9 5` (kind 16 is unsigned, so
`BoundsAgree` leaves no other panic). -/
theorem genG19_boundsPanic_witness :
    ∃ mm' m', stepLoc GenG2.env lc s0 (val 11) = .panic (.bounds 16 9 5) mm' ∧
      PStar H L ps.toList 0 m0 m' ∧ PPanics H L ps.toList 0 m' (.bounds 16 9 5) := by
  obtain ⟨hc, hav, hsl, hm3, hb, hv11, hi0, hop, hk0, hrun, hall⟩ := facts
  obtain ⟨mm', hs⟩ := isPanic_spec hrun
  obtain ⟨e', m', hag, hstar, hpan⟩ := g19_boundsPanic (H := H) (env := GenG2.env) hc
    (g19Env hc hav hsl) hm3 hb hi0 hv11 hop locMatch0 (g19Inv0 hk0) (boundsOK hall) hs
  rcases hag with rfl | ⟨k, x, y, he, -, -, hk16, -⟩
  · exact ⟨mm', m', hs, hstar, hpan⟩
  · cases he
    omega

end GoFV.Proof.Witness.GenG19
