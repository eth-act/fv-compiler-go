import GoFV.Proof.Gen.G35
import GoFV.Proof.Witness.GenG13

/-!
# Non-vacuity witness: slice G35 of the genssa validator on `regexp/syntax.(*InstOp).String`

`std/std/regexp/syntax/%28%2AInstOp%29.String,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`;
`regexp/syntax/prog.go`, the pointer method wrapping):

```go
func (i InstOp) String() string {
	if uint(i) >= uint(len(instOpNames)) {
		return ""
	}
	return instOpNames[i]
}
```

Block `b2`: `v3 = SB`, `v16 = MOVBUload v6` (`i`, `MOVBU (R0), R2`), `v21 = MOVDreg v16`
(`uint(i)`, `MOVD R2, R3`), `v44 = LDP instOpNames(SB)` (the slice's pointer and length into
`(R4, R5)`), `v4 = Select1 v44` (the length, `R5`), `v5 = Select0 v44` (the pointer, `R4`),
`InlMark`, `v28 = CMP v21 v4`; then `b7` (`i` in range) starts with `v29 = MOVDreg v16`
(`MOVD R2, R2`). Before `v4` (index 4), G35's table `uL35` is `[(3, 8, false), (2, 8, false)]`:
`R3` and `R2` are zero-extended from 8 bits. G34 empties its table across `LDP` and its selects
(`uStep34` gives `[]` across `v4`), so `b7` starts with nothing, `v29` finds no entry for `R2` and
`checkG34` rejects the function; G35 keeps both entries across `v44`, `v4` and `v5`, which write
only `R4` and `R5`, and `checkG35` accepts the function with the PC table `tab` and the class
table `kt`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g35_facts`),
`stepLoc` runs `v4` from a state with the length `7` in `R5` (and the byte `i = 0x2a` in `R2`, its
64-bit copy in `R3`) to `R5 = 7`, keeping `R2 = 0x2a` (8 bits). On a framed activation with
`G28Env`, `g35_value` runs `v4` (no code; `genG35_witness`): G35's table after `v4` is still
`[(3, 8, false), (2, 8, false)]` and gives the whole `X2 = 0x2a` (`LocMatch` alone gives only its
low 8 bits).
-/

namespace GoFV.Proof.Witness.GenG35

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/regexp/syntax/%28%2AInstOp%29.String,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "regexp/syntax"
func "(*InstOp).String" 1 0 0
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
config localpkg "regexp/syntax"
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
type t3 UINT8 1 1 0 comparable,named "InstOp" "regexp/syntax.InstOp"
type t2 PTR 8 8 8 hasptr,direct,comparable "*InstOp" "*regexp/syntax.InstOp" t3
type t4 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t1 FUNC 8 8 8 hasptr,direct "method(*InstOp) func() string" "method(*regexp/syntax.InstOp) func() string" 1 0 1
field 0 "i" t2 ? 0
field 1 "" t4 ? 0
aux a2 sym "regexp/syntax.(*InstOp).String" "regexp/syntax.(*InstOp).String" 1 - 0 - - - - 0
posbase p7 "regexp/syntax/prog.go" 1 1 -1
aux a3 name "i" "i" PPARAM t2 0 1 used p7:55:7:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t4 0 1 - p7:55:26:0:0
aux a1 call "AuxCall{regexp/syntax.(*InstOp).String}" a2 1 1 1 8 8 1 2
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
posbase p1 "<autogenerated>" 1 1 -1
type t35 PTR 8 8 8 hasptr,direct,comparable "**InstOp" "**regexp/syntax.InstOp" t2
type t36 PTR 8 8 8 hasptr,direct,comparable "*string" "*string" t4
aux a5 str "" "" "go:string.\"\""
type t38 SLICE 24 8 8 hasptr "[]string" "[]string" t4
type t37 PTR 8 8 8 hasptr,direct,comparable "*[]string" "*[]string" t38
aux a6 sym "regexp/syntax.instOpNames" "regexp/syntax.instOpNames" 0 - 0 - - - - 0
posbase p484 "regexp/syntax/prog.go" 1 1 375
aux a8 sym "runtime.panicwrap" "runtime.panicwrap" 1 - 0 - - - - 0
aux a7 call "AuxCall{runtime.panicwrap}" a8 1 0 0 8 0 0 0
type t39 RESULTS ? ? ? - "string,mem" "" 2 t4,t30
slot s1 a3 t2 0 - 0
aux a9 name "i" "i" PAUTO t3 0 1 used p484:55:7:0:0
slot s2 a9 t3 0 - 0
aux a10 name "~r0" "~r0" PAUTO t4 0 1 - p484:55:26:0:0
slot s3 a10 t4 0 - 0
f b1 t1 a1 39 8
typs Bool=t5,Int8=t6,Int16=t7,Int32=t8,Int64=t9,UInt8=t10,UInt16=t11,UInt32=t12,UInt64=t13,Int=t14,Float32=t15,Float64=t16,UInt=t17,Uintptr=t18,String=t4,BytePtr=t19,Int32Ptr=t20,UInt32Ptr=t21,IntPtr=t22,UintptrPtr=t23,Float32Ptr=t24,Float64Ptr=t25,BytePtrPtr=t26,Complex64=t27,Complex128=t28,UnsafePtr=t29,Mem=t30,Flags=t31,Void=t32,Int128=t33,ResultMem=t34
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 ConstString t4 0 a5 p0:0:0:0:0 1 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:0:0 1 v6,v8
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v24 Addr t37 0 a6 p0:0:0:0:0 1 v3
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:1
v v13 Copy t2 0 - p1:1:0:2:0 1 v6
v v14 Copy t30 0 - p1:1:0:2:0 6 v1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v13,v14
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v14
v v17 InlMark t32 375 - p1:1:0:1:0 0 v14
v v19 Load t38 0 - p484:56:24:0:0 1 v18,v14
v v20 SliceLen t14 0 - p484:56:24:0:0 1 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v22 Copy t17 0 - p484:56:24:2:0 1 v20
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v22,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v10 Copy t30 0 - p1:1:0:2:0 1 v1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v10
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v25 Copy t30 0 - p484:59:20:2:0 3 v14
v v26 Load t38 0 - p484:59:20:0:0 2 v24,v25
v v27 Copy t3 0 - p484:59:20:2:0 1 v16
v v28 SliceLen t14 0 - p484:59:20:0:0 2 v26
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v27
v v30 IsInBounds t5 0 - p484:59:20:0:0 1 v29,v28
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v38 Phi t30 0 - p1:1:0:0:0 1 v14,v35
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v38
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v26
v v34 PtrIndex t36 0 - p484:59:20:0:0 1 v33,v29
v v35 Copy t30 0 - p484:59:20:2:0 2 v25
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v35
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v31 Copy t30 0 - p484:59:20:2:0 1 v25
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v28,v31
names s1,s2,s3
named s1 v6,v13
named s2 v16,v27
named s3 v7,v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts 3344556677=v8,4455667788=v7
freev -
freeb -
dcllen 5
zvar v6:1,v8:1
end
pass 1 "number lines"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 ConstString t4 0 a5 p0:0:0:0:0 1 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:1:0 1 v6,v8
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v24 Addr t37 0 a6 p0:0:0:0:0 1 v3
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:1
v v13 Copy t2 0 - p1:1:0:2:0 1 v6
v v14 Copy t30 0 - p1:1:0:2:0 6 v1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v13,v14
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v14
v v17 InlMark t32 375 - p1:1:0:0:0 0 v14
v v19 Load t38 0 - p484:56:24:1:0 1 v18,v14
v v20 SliceLen t14 0 - p484:56:24:0:0 1 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v22 Copy t17 0 - p484:56:24:2:0 1 v20
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v22,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v10 Copy t30 0 - p1:1:0:2:0 1 v1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v10
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v25 Copy t30 0 - p484:59:20:2:0 3 v14
v v26 Load t38 0 - p484:59:20:1:0 2 v24,v25
v v27 Copy t3 0 - p484:59:20:2:0 1 v16
v v28 SliceLen t14 0 - p484:59:20:0:0 2 v26
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v27
v v30 IsInBounds t5 0 - p484:59:20:0:0 1 v29,v28
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v38 Phi t30 0 - p1:1:0:0:0 1 v14,v35
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v38
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v26
v v34 PtrIndex t36 0 - p484:59:20:0:0 1 v33,v29
v v35 Copy t30 0 - p484:59:20:2:0 2 v25
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v35
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v31 Copy t30 0 - p484:59:20:2:0 1 v25
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v28,v31
names s1,s2,s3
named s1 v6,v13
named s2 v16,v27
named s3 v7,v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts 3344556677=v8,4455667788=v7
freev -
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1,v8:1
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 17 -
v v2 SP t18 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 3 -
v v7 ConstString t4 0 a5 p0:0:0:0:0 1 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:1:0 1 v6,v8
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v24 Addr t37 0 a6 p0:0:0:0:0 1 v3
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:1
v v13 Copy t2 0 - p1:1:0:2:0 0 v6
v v14 Copy t30 0 - p1:1:0:2:0 0 v1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 3 v15,v1
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 1 v18,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 2 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v22 Copy t17 0 - p484:56:24:2:0 0 v20
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v10 Copy t30 0 - p1:1:0:2:0 0 v1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v25 Copy t30 0 - p484:59:20:2:0 0 v1
v v26 Load t38 0 - p484:59:20:1:0 2 v24,v1
v v27 Copy t3 0 - p484:59:20:2:0 0 v16
v v28 SliceLen t14 0 - p484:59:20:0:0 2 v26
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:0:0 1 v29,v28
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v38 Copy t30 0 - p1:1:0:0:0 0 v1
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v26
v v34 PtrIndex t36 0 - p484:59:20:0:0 1 v33,v29
v v35 Copy t30 0 - p484:59:20:2:0 0 v1
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v31 Copy t30 0 - p484:59:20:2:0 0 v1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v28,v1
names s1,s2,s3
named s1 v6,v6
named s2 v16,v16
named s3 v7,v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts 3344556677=v8,4455667788=v7
freev -
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1,v8:1
end
pass 3 "early deadcode"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 ConstString t4 0 a5 p0:0:0:0:0 1 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:1:0 1 v6,v8
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v24 Addr t37 0 a6 p0:0:0:0:0 1 v3
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 1 v18,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 1 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v26 Load t38 0 - p484:59:20:1:0 2 v24,v1
v v28 SliceLen t14 0 - p484:59:20:0:0 2 v26
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:0:0 1 v29,v28
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v26
v v34 PtrIndex t36 0 - p484:59:20:0:0 1 v33,v29
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v28,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts 3344556677=v8,4455667788=v7
freev v31,v35,v38,v27,v25,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1,v8:1
end
pass 4 "short circuit"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 ConstString t4 0 a5 p0:0:0:0:0 1 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:1:0 1 v6,v8
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v24 Addr t37 0 a6 p0:0:0:0:0 1 v3
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 1 v18,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 1 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v26 Load t38 0 - p484:59:20:1:0 2 v24,v1
v v28 SliceLen t14 0 - p484:59:20:0:0 2 v26
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:0:0 1 v29,v28
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v26
v v34 PtrIndex t36 0 - p484:59:20:0:0 1 v33,v29
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v28,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts 3344556677=v8,4455667788=v7
freev v31,v35,v38,v27,v25,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1,v8:1
end
pass 5 "decompose user"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 ConstString t4 0 a5 p0:0:0:0:0 1 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:1:0 1 v6,v8
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v24 Addr t37 0 a6 p0:0:0:0:0 1 v3
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 1 v18,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 1 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v26 Load t38 0 - p484:59:20:1:0 2 v24,v1
v v28 SliceLen t14 0 - p484:59:20:0:0 2 v26
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:0:0 1 v29,v28
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v26
v v34 PtrIndex t36 0 - p484:59:20:0:0 1 v33,v29
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v28,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts 3344556677=v8,4455667788=v7
freev v31,v35,v38,v27,v25,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1,v8:1
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 ConstString t4 0 a5 p0:0:0:0:0 1 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:1:0 1 v6,v8
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v24 Addr t37 0 a6 p0:0:0:0:0 1 v3
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 1 v18,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 1 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v26 Load t38 0 - p484:59:20:1:0 2 v24,v1
v v28 SliceLen t14 0 - p484:59:20:0:0 2 v26
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:0:0 1 v29,v28
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v26
v v34 PtrIndex t36 0 - p484:59:20:0:0 1 v33,v29
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v28,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts 3344556677=v8,4455667788=v7
freev v31,v35,v38,v27,v25,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1,v8:1
end
pass 7 "opt"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v24 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 1 v18,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 1 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v26 Load t38 0 - p484:59:20:1:0 2 v24,v1
v v28 SliceLen t14 0 - p484:59:20:0:0 2 v26
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:0:0 1 v29,v28
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v26
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
v v27 Mul64 t14 0 - p484:59:20:0:0 1 v29,v25
v v25 Const64 t14 16 - p484:59:20:0:0 1 -
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v28,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 8 "zero arg cse"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v24 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v25 Const64 t14 16 - p484:59:20:0:0 1 -
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 1 v18,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 1 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v26 Load t38 0 - p484:59:20:1:0 2 v24,v1
v v28 SliceLen t14 0 - p484:59:20:0:0 2 v26
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:0:0 1 v29,v28
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v26
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
v v27 Mul64 t14 0 - p484:59:20:0:0 1 v29,v25
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v28,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 9 "opt deadcode"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v24 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v25 Const64 t14 16 - p484:59:20:0:0 1 -
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 1 v18,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 1 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v26 Load t38 0 - p484:59:20:1:0 2 v24,v1
v v28 SliceLen t14 0 - p484:59:20:0:0 2 v26
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:0:0 1 v29,v28
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v26
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
v v27 Mul64 t14 0 - p484:59:20:0:0 1 v29,v25
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v28,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 10 "generic cse"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 2 v3
v v24 Addr t37 0 a6 p0:0:0:0:0 0 v3
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v25 Const64 t14 16 - p484:59:20:0:0 1 -
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 3 v18,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 3 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v26 Load t38 0 - p484:59:20:2:0 0 v18,v1
v v28 SliceLen t14 0 - p484:59:20:2:0 0 v19
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:1:0 1 v29,v20
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v19
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
v v27 Mul64 t14 0 - p484:59:20:0:0 1 v29,v25
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v20,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 11 "phiopt"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 2 v3
v v24 Addr t37 0 a6 p0:0:0:0:0 0 v3
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v25 Const64 t14 16 - p484:59:20:0:0 1 -
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 3 v18,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 3 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v26 Load t38 0 - p484:59:20:2:0 0 v18,v1
v v28 SliceLen t14 0 - p484:59:20:2:0 0 v19
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:1:0 1 v29,v20
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v19
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
v v27 Mul64 t14 0 - p484:59:20:0:0 1 v29,v25
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v20,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 12 "gcse deadcode"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 8 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v25 Const64 t14 16 - p484:59:20:0:0 1 -
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 2 v18,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 3 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:1:0 1 v29,v20
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v19
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
v v27 Mul64 t14 0 - p484:59:20:0:0 1 v29,v25
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v20,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v28,v26,v24,v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 13 "nilcheckelim"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 7 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v25 Const64 t14 16 - p484:59:20:0:0 1 -
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v15 Copy t2 0 - p1:1:0:0:0 1 v6
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 2 v18,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 3 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 If p484:59:20:0:0 1 0 - v30 b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:1:0 1 v29,v20
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v19
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
v v27 Mul64 t14 0 - p484:59:20:0:0 1 v29,v25
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v20,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v28,v26,v24,v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 14 "prove"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 7 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v25 Const64 t14 16 - p484:59:20:0:0 1 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v15 Copy t2 0 - p1:1:0:0:0 1 v6
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 2 v18,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 3 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 3 v16
v v30 IsInBounds t5 0 - p484:59:20:1:0 0 v29,v20
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Mul64 t14 0 - p484:59:20:0:0 1 v29,v25
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v19
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v20,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v28,v26,v24,v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 15 "divisible"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 7 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v25 Const64 t14 16 - p484:59:20:0:0 1 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 2 v18,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 2 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 2 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Mul64 t14 0 - p484:59:20:0:0 1 v29,v25
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v19
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v20,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v30,v15,v28,v26,v24,v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 16 "divmod"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 7 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v25 Const64 t14 16 - p484:59:20:0:0 1 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 2 v18,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 2 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 2 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Mul64 t14 0 - p484:59:20:0:0 1 v29,v25
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v19
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v20,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v30,v15,v28,v26,v24,v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 17 "middle opt"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 7 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 2 v18,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 2 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 2 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Lsh64x64 t14 1 - p484:59:20:0:0 1 v29,v30
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v19
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v20,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v25,v15,v28,v26,v24,v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 18 "known bits"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 7 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 2 v18,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 2 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 2 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Lsh64x64 t14 1 - p484:59:20:0:0 1 v29,v30
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v19
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v20,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v25,v15,v28,v26,v24,v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 19 "early fuse"
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 7 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 2 v18,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 2 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 2 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 1 v7,v36
v v39 MakeResult t39 0 - p1:1:0:0:0 1 v37,v1
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Lsh64x64 t14 1 - p484:59:20:0:0 1 v29,v30
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v19
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v20,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v25,v15,v28,v26,v24,v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 20 "expand calls"
aux a11 nameoff "i+0" a3 0
type t40 RESULTS ? ? ? - "*uint8,int,mem" "" 3 t19,t14,t30
f b1 t1 a1 39 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 8 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v7 StringMake t4 0 - p0:0:0:0:0 1 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 1 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v25 SP t18 0 - p0:0:0:0:0 2 -
v v15 OffPtr t35 0 - p0:0:0:0:0 0 v25
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 Load t38 0 - p484:56:24:1:0 2 v18,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v20 SliceLen t14 0 - p484:56:24:0:0 2 v19
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v20,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 2 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 Phi t4 0 - p1:1:0:0:0 2 v7,v36
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v26,v24,v1
v v28 LocalAddr t36 0 a4 p1:1:0:0:0 0 v25,v1
v v26 StringPtr t19 0 - p1:1:0:0:0 1 v37
v v24 StringLen t14 0 - p1:1:0:2:0 1 v37
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Lsh64x64 t14 1 - p484:59:20:0:0 1 v29,v30
v v33 SlicePtr t36 0 - p484:59:20:0:0 1 v19
v v34 AddPtr t36 0 - p484:59:20:0:0 1 v33,v27
v v36 Load t4 0 - p484:59:20:0:0 1 v34,v1
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v20,v1
names s1,s2,s3
named s1 v6
named s2 v16
named s3 v7,v36,v37
splits -
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts 0=v15
freev v9,v8,v10,v22,v14,v13,v5,v4,v2
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 5
zvar v6:1
end
pass 21 "decompose builtin"
aux a12 name "~r0.ptr" "~r0.ptr" PAUTO t19 0 3 used p484:55:26:0:0
slot s4 a12 t19 0 s3 0
aux a13 name "~r0.len" "~r0.len" PAUTO t14 0 3 used p484:55:26:0:0
slot s5 a13 t14 0 s3 8
f b1 t1 a1 44 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 11 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 2 -
v v35 Const64 t14 0 - p0:0:0:0:0 2 -
v v7 StringMake t4 0 - p0:0:0:0:0 0 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 3 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v25 SP t18 0 - p0:0:0:0:0 2 -
v v15 OffPtr t35 0 - p0:0:0:0:0 0 v25
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 SliceMake t38 0 - p484:56:24:1:0 0 v5,v4,v40
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v4,v21
v v5 Load t36 0 - p484:56:24:1:0 2 v18,v1
v v4 Load t14 0 - p484:56:24:1:0 3 v2,v1
v v2 OffPtr t22 8 - p484:56:24:1:0 1 v18
v v40 Load t14 0 - p484:56:24:1:0 1 v41,v1
v v41 OffPtr t22 16 - p484:56:24:1:0 1 v18
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 2 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 StringMake t4 0 - p1:1:0:0:0 0 v9,v8
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v28 LocalAddr t36 0 a4 p1:1:0:0:0 0 v25,v1
v v9 Phi t19 0 - p1:1:0:2:0 2 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 2 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Lsh64x64 t14 1 - p484:59:20:0:0 1 v29,v30
v v34 AddPtr t36 0 - p484:59:20:0:0 2 v5,v27
v v36 StringMake t4 0 - p484:59:20:0:0 0 v42,v43
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
v v42 Load t19 0 - p484:59:20:0:0 2 v34,v1
v v43 Load t14 0 - p484:59:20:0:0 2 v44,v1
v v44 OffPtr t22 8 - p484:59:20:0:0 1 v34
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v4,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts 0=v15
freev v13,v14,v33,v24,v26,v20,v22,v10
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 22 "softfloat"
f b1 t1 a1 44 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 11 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 2 -
v v35 Const64 t14 0 - p0:0:0:0:0 2 -
v v7 StringMake t4 0 - p0:0:0:0:0 0 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 3 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v25 SP t18 0 - p0:0:0:0:0 2 -
v v15 OffPtr t35 0 - p0:0:0:0:0 0 v25
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 SliceMake t38 0 - p484:56:24:1:0 0 v5,v4,v40
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v4,v21
v v5 Load t36 0 - p484:56:24:1:0 2 v18,v1
v v4 Load t14 0 - p484:56:24:1:0 3 v2,v1
v v2 OffPtr t22 8 - p484:56:24:1:0 1 v18
v v40 Load t14 0 - p484:56:24:1:0 1 v41,v1
v v41 OffPtr t22 16 - p484:56:24:1:0 1 v18
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 2 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 StringMake t4 0 - p1:1:0:0:0 0 v9,v8
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v28 LocalAddr t36 0 a4 p1:1:0:0:0 0 v25,v1
v v9 Phi t19 0 - p1:1:0:2:0 2 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 2 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Lsh64x64 t14 1 - p484:59:20:0:0 1 v29,v30
v v34 AddPtr t36 0 - p484:59:20:0:0 2 v5,v27
v v36 StringMake t4 0 - p484:59:20:0:0 0 v42,v43
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
v v42 Load t19 0 - p484:59:20:0:0 2 v34,v1
v v43 Load t14 0 - p484:59:20:0:0 2 v44,v1
v v44 OffPtr t22 8 - p484:59:20:0:0 1 v34
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v4,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts 0=v15
freev v13,v14,v33,v24,v26,v20,v22,v10
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 23 "branchelim"
f b1 t1 a1 44 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 11 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 2 -
v v35 Const64 t14 0 - p0:0:0:0:0 2 -
v v7 StringMake t4 0 - p0:0:0:0:0 0 v31,v35
v v18 Addr t37 0 a6 p0:0:0:0:0 3 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v25 SP t18 0 - p0:0:0:0:0 2 -
v v15 OffPtr t35 0 - p0:0:0:0:0 0 v25
b b2 If p484:56:24:0:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v19 SliceMake t38 0 - p484:56:24:1:0 0 v5,v4,v40
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ZeroExt8to64 t17 0 - p484:56:10:0:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v4,v21
v v5 Load t36 0 - p484:56:24:1:0 2 v18,v1
v v4 Load t14 0 - p484:56:24:1:0 3 v2,v1
v v2 OffPtr t22 8 - p484:56:24:1:0 1 v18
v v40 Load t14 0 - p484:56:24:1:0 1 v41,v1
v v41 OffPtr t22 16 - p484:56:24:1:0 1 v18
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 2 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v37 StringMake t4 0 - p1:1:0:0:0 0 v9,v8
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v28 LocalAddr t36 0 a4 p1:1:0:0:0 0 v25,v1
v v9 Phi t19 0 - p1:1:0:2:0 2 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 2 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Lsh64x64 t14 1 - p484:59:20:0:0 1 v29,v30
v v34 AddPtr t36 0 - p484:59:20:0:0 2 v5,v27
v v36 StringMake t4 0 - p484:59:20:0:0 0 v42,v43
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
v v42 Load t19 0 - p484:59:20:0:0 2 v34,v1
v v43 Load t14 0 - p484:59:20:0:0 2 v44,v1
v v44 OffPtr t22 8 - p484:59:20:0:0 1 v34
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v4,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts 0=v15
freev v13,v14,v33,v24,v26,v20,v22,v10
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 24 "late opt"
f b1 t1 a1 44 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v18 Addr t37 0 a6 p0:0:0:0:0 2 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:1:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ZeroExt8to64 t17 0 - p484:56:10:1:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v4,v21
v v5 Load t36 0 - p484:56:24:1:0 1 v18,v1
v v4 Load t14 0 - p484:56:24:1:0 2 v2,v1
v v2 OffPtr t22 8 - p484:56:24:1:0 1 v18
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 2 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Lsh64x64 t14 1 - p484:59:20:0:0 1 v29,v30
v v34 AddPtr t36 0 - p484:59:20:0:0 2 v5,v27
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
v v42 Load t19 0 - p484:59:20:0:0 1 v34,v1
v v43 Load t14 0 - p484:59:20:0:0 1 v44,v1
v v44 OffPtr t22 8 - p484:59:20:0:0 1 v34
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v4,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v36,v28,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 25 "dead auto elim"
f b1 t1 a1 44 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v18 Addr t37 0 a6 p0:0:0:0:0 2 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:1:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ZeroExt8to64 t17 0 - p484:56:10:1:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v4,v21
v v5 Load t36 0 - p484:56:24:1:0 1 v18,v1
v v4 Load t14 0 - p484:56:24:1:0 2 v2,v1
v v2 OffPtr t22 8 - p484:56:24:1:0 1 v18
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 2 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Lsh64x64 t14 1 - p484:59:20:0:0 1 v29,v30
v v34 AddPtr t36 0 - p484:59:20:0:0 2 v5,v27
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
v v42 Load t19 0 - p484:59:20:0:0 1 v34,v1
v v43 Load t14 0 - p484:59:20:0:0 1 v44,v1
v v44 OffPtr t22 8 - p484:59:20:0:0 1 v34
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v4,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v36,v28,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 26 "sccp"
f b1 t1 a1 44 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v18 Addr t37 0 a6 p0:0:0:0:0 2 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:1:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ZeroExt8to64 t17 0 - p484:56:10:1:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v4,v21
v v5 Load t36 0 - p484:56:24:1:0 1 v18,v1
v v4 Load t14 0 - p484:56:24:1:0 2 v2,v1
v v2 OffPtr t22 8 - p484:56:24:1:0 1 v18
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 First p484:59:20:1:0 1 0 - - b7:0,b8:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 2 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Lsh64x64 t14 1 - p484:59:20:0:0 1 v29,v30
v v34 AddPtr t36 0 - p484:59:20:0:0 2 v5,v27
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
v v42 Load t19 0 - p484:59:20:0:0 1 v34,v1
v v43 Load t14 0 - p484:59:20:0:0 1 v44,v1
v v44 OffPtr t22 8 - p484:59:20:0:0 1 v34
b b8 Exit p484:59:20:0:0 0 0 - v32 - b4:1
v v32 PanicBounds t30 0 - p484:59:20:0:0 1 v29,v4,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v36,v28,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb -
cache postorder b3,b6,b5,b7,b8,b4,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b4,b8:b4
cache sdom b1:-:b2:-:2:47,b2:b1:b4:b3:5:38,b3:b1:-:-:41:44,b4:b2:b8:b5:8:23,b5:b2:-:b6:26:29,b6:b2:-:-:32:35,b7:b4:-:-:17:20,b8:b4:-:b7:11:14
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 27 "generic deadcode"
f b1 t1 a1 44 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 8 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v18 Addr t37 0 a6 p0:0:0:0:0 2 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:1:0 0 0 - v23 b5:0,b4:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ZeroExt8to64 t17 0 - p484:56:10:1:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v4,v21
v v5 Load t36 0 - p484:56:24:1:0 1 v18,v1
v v4 Load t14 0 - p484:56:24:1:0 1 v2,v1
v v2 OffPtr t22 8 - p484:56:24:1:0 1 v18
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 Plain p484:59:20:1:0 0 0 - - b7:0 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 1 v16
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b4:0
v v27 Lsh64x64 t14 1 - p484:59:20:0:0 1 v29,v30
v v34 AddPtr t36 0 - p484:59:20:0:0 2 v5,v27
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
v v42 Load t19 0 - p484:59:20:0:0 1 v34,v1
v v43 Load t14 0 - p484:59:20:0:0 1 v44,v1
v v44 OffPtr t22 8 - p484:59:20:0:0 1 v34
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v32,v36,v28,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b8
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 28 "late fuse"
f b1 t1 a1 44 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 8 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v18 Addr t37 0 a6 p0:0:0:0:0 2 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:1:0 0 0 - v23 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ZeroExt8to64 t17 0 - p484:56:10:1:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v4,v21
v v5 Load t36 0 - p484:56:24:1:0 1 v18,v1
v v4 Load t14 0 - p484:56:24:1:0 1 v2,v1
v v2 OffPtr t22 8 - p484:56:24:1:0 1 v18
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 BlockInvalid p484:59:20:1:0 0 0 - - - -
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 1 v16
v v27 Lsh64x64 t14 1 - p484:59:20:1:0 1 v29,v30
v v34 AddPtr t36 0 - p484:59:20:0:0 2 v5,v27
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
v v42 Load t19 0 - p484:59:20:0:0 1 v34,v1
v v43 Load t14 0 - p484:59:20:0:0 1 v44,v1
v v44 OffPtr t22 8 - p484:59:20:0:0 1 v34
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v32,v36,v28,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b8
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 29 "check bce"
f b1 t1 a1 44 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 8 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v18 Addr t37 0 a6 p0:0:0:0:0 2 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:1:0 0 0 - v23 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ZeroExt8to64 t17 0 - p484:56:10:1:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v4,v21
v v5 Load t36 0 - p484:56:24:1:0 1 v18,v1
v v4 Load t14 0 - p484:56:24:1:0 1 v2,v1
v v2 OffPtr t22 8 - p484:56:24:1:0 1 v18
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 BlockInvalid p484:59:20:1:0 0 0 - - - -
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 1 v16
v v27 Lsh64x64 t14 1 - p484:59:20:1:0 1 v29,v30
v v34 AddPtr t36 0 - p484:59:20:0:0 2 v5,v27
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
v v42 Load t19 0 - p484:59:20:0:0 1 v34,v1
v v43 Load t14 0 - p484:59:20:0:0 1 v44,v1
v v44 OffPtr t22 8 - p484:59:20:0:0 1 v34
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v32,v36,v28,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b8
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 30 "dse"
f b1 t1 a1 44 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 8 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v18 Addr t37 0 a6 p0:0:0:0:0 2 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:1:0 0 0 - v23 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ZeroExt8to64 t17 0 - p484:56:10:1:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v4,v21
v v5 Load t36 0 - p484:56:24:1:0 1 v18,v1
v v4 Load t14 0 - p484:56:24:1:0 1 v2,v1
v v2 OffPtr t22 8 - p484:56:24:1:0 1 v18
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 BlockInvalid p484:59:20:1:0 0 0 - - - -
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 1 v16
v v27 Lsh64x64 t14 1 - p484:59:20:1:0 1 v29,v30
v v34 AddPtr t36 0 - p484:59:20:0:0 2 v5,v27
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
v v42 Load t19 0 - p484:59:20:0:0 1 v34,v1
v v43 Load t14 0 - p484:59:20:0:0 1 v44,v1
v v44 OffPtr t22 8 - p484:59:20:0:0 1 v34
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v32,v36,v28,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b8
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 31 "memcombine"
f b1 t1 a1 44 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 8 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v18 Addr t37 0 a6 p0:0:0:0:0 2 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:1:0 0 0 - v23 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ZeroExt8to64 t17 0 - p484:56:10:1:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v4,v21
v v5 Load t36 0 - p484:56:24:1:0 1 v18,v1
v v4 Load t14 0 - p484:56:24:1:0 1 v2,v1
v v2 OffPtr t22 8 - p484:56:24:1:0 1 v18
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 BlockInvalid p484:59:20:1:0 0 0 - - - -
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 1 v16
v v27 Lsh64x64 t14 1 - p484:59:20:1:0 1 v29,v30
v v34 AddPtr t36 0 - p484:59:20:0:0 2 v5,v27
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
v v42 Load t19 0 - p484:59:20:0:0 1 v34,v1
v v43 Load t14 0 - p484:59:20:0:0 1 v44,v1
v v44 OffPtr t22 8 - p484:59:20:0:0 1 v34
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v32,v36,v28,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b8
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 32 "writebarrier"
f b1 t1 a1 44 8
b b1 If p1:1:0:0:0 0 0 - v38 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 8 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ConstNil t19 0 - p0:0:0:0:0 1 -
v v35 Const64 t14 0 - p0:0:0:0:0 1 -
v v18 Addr t37 0 a6 p0:0:0:0:0 2 v3
v v38 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b2 If p484:56:24:1:0 0 0 - v23 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 Load t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ZeroExt8to64 t17 0 - p484:56:10:1:0 1 v16
v v23 Leq64U t5 0 - p484:56:13:0:0 1 v4,v21
v v5 Load t36 0 - p484:56:24:1:0 1 v18,v1
v v4 Load t14 0 - p484:56:24:1:0 1 v2,v1
v v2 OffPtr t22 8 - p484:56:24:1:0 1 v18
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 BlockInvalid p484:59:20:1:0 0 0 - - - -
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ZeroExt8to64 t14 0 - p484:59:20:0:0 1 v16
v v27 Lsh64x64 t14 1 - p484:59:20:1:0 1 v29,v30
v v34 AddPtr t36 0 - p484:59:20:0:0 2 v5,v27
v v30 Const64 t13 4 - p484:59:20:0:0 1 -
v v42 Load t19 0 - p484:59:20:0:0 1 v34,v1
v v43 Load t14 0 - p484:59:20:0:0 1 v44,v1
v v44 OffPtr t22 8 - p484:59:20:0:0 1 v34
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v32,v36,v28,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b8
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 33 "lower"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 8 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ARM64MOVDconst t19 0 - p0:0:0:0:0 1 -
v v35 ARM64MOVDconst t14 0 - p0:0:0:0:0 1 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVBUreg t17 0 - p484:56:10:1:0 1 v16
v v5 ARM64MOVDload t36 0 a6 p484:56:24:1:0 1 v3,v1
v v4 ARM64MOVDload t14 8 a6 p484:56:24:1:0 1 v3,v1
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 BlockInvalid p484:59:20:1:0 0 0 - - - -
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVBUreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 2 v5,v29
v v42 ARM64MOVDload t19 0 - p484:59:20:0:0 1 v34,v1
v v43 ARM64MOVDload t14 8 - p484:59:20:0:0 1 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v44,v30,v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b8
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 34 "addressing modes"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 8 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ARM64MOVDconst t19 0 - p0:0:0:0:0 1 -
v v35 ARM64MOVDconst t14 0 - p0:0:0:0:0 1 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVBUreg t17 0 - p484:56:10:1:0 1 v16
v v5 ARM64MOVDload t36 0 a6 p484:56:24:1:0 1 v3,v1
v v4 ARM64MOVDload t14 8 a6 p484:56:24:1:0 1 v3,v1
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 BlockInvalid p484:59:20:1:0 0 0 - - - -
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVBUreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 2 v5,v29
v v42 ARM64MOVDload t19 0 - p484:59:20:0:0 1 v34,v1
v v43 ARM64MOVDload t14 8 - p484:59:20:0:0 1 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v44,v30,v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b8
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 35 "late lower"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 8 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 ARM64MOVDload t36 0 a6 p484:56:24:1:0 1 v3,v1
v v4 ARM64MOVDload t14 8 a6 p484:56:24:1:0 1 v3,v1
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 BlockInvalid p484:59:20:1:0 0 0 - - - -
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 2 v5,v29
v v42 ARM64MOVDload t19 0 - p484:59:20:0:0 1 v34,v1
v v43 ARM64MOVDload t14 8 - p484:59:20:0:0 1 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v44,v30,v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b8
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 36 "pair"
type t41 TUPLE ? ? ? - "*string,int" "" t36 t14
type t42 TUPLE ? ? ? - "*uint8,int" "" t19 t14
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 BlockInvalid p484:59:20:1:0 0 0 - - - -
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b8
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache auxmap -:1,a3:2,a6:3
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 38 "lowered cse"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b6:b2,b7:b2
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b3:b1:-:b2:5:8,b5:b2:-:b6:20:23,b6:b2:-:-:26:29,b7:b2:-:b5:14:17
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 39 "elim unread autos"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b6:b2,b7:b2
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b3:b1:-:b2:5:8,b5:b2:-:b6:20:23,b6:b2:-:-:26:29,b7:b2:-:b5:14:17
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b6:b2,b7:b2
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b3:b1:-:b2:5:8,b5:b2:-:b6:20:23,b6:b2:-:-:26:29,b7:b2:-:b5:14:17
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 41 "lowered deadcode"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b6:b2,b7:b2
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b3:b1:-:b2:5:8,b5:b2:-:b6:20:23,b6:b2:-:-:26:29,b7:b2:-:b5:14:17
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 42 "checkLower"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b6:b2,b7:b2
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b3:b1:-:b2:5:8,b5:b2:-:b6:20:23,b6:b2:-:-:26:29,b7:b2:-:b5:14:17
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 43 "loop invariant"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b6:b2,b7:b2
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b3:b1:-:b2:5:8,b5:b2:-:b6:20:23,b6:b2:-:-:26:29,b7:b2:-:b5:14:17
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b6:b2,b7:b2
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b3:b1:-:b2:5:8,b5:b2:-:b6:20:23,b6:b2:-:-:26:29,b7:b2:-:b5:14:17
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 45 "tighten"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
v v3 SB t18 0 - p0:0:0:0:0 1 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b6:b2,b7:b2
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b3:b1:-:b2:5:8,b5:b2:-:b6:20:23,b6:b2:-:-:26:29,b7:b2:-:b5:14:17
cache loopnest 9 0 - -
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 46 "late deadcode"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
v v3 SB t18 0 - p0:0:0:0:0 1 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b6:b2,b7:b2
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b3:b1:-:b2:5:8,b5:b2:-:b6:20:23,b6:b2:-:-:26:29,b7:b2:-:b5:14:17
cache loopnest 9 0 - -
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 47 "critical"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
v v3 SB t18 0 - p0:0:0:0:0 1 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b6:b2,b7:b2
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b3:b1:-:b2:5:8,b5:b2:-:b6:20:23,b6:b2:-:-:26:29,b7:b2:-:b5:14:17
cache loopnest 9 0 - -
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 48 "phi tighten"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
v v3 SB t18 0 - p0:0:0:0:0 1 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b6:b2,b7:b2
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b3:b1:-:b2:5:8,b5:b2:-:b6:20:23,b6:b2:-:-:26:29,b7:b2:-:b5:14:17
cache loopnest 9 0 - -
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 49 "likelyadjust"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
v v3 SB t18 0 - p0:0:0:0:0 1 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b2,b6:b2,b7:b2
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b3:b1:-:b2:5:8,b5:b2:-:b6:20:23,b6:b2:-:-:26:29,b7:b2:-:b5:14:17
cache loopnest 9 0 - -
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
dcllen 7
zvar v6:1
end
pass 50 "layout"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
v v3 SB t18 0 - p0:0:0:0:0 1 -
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b5:b2,b7:b2,b6:b2,b3:b1
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b5:b2:-:b6:20:23,b7:b2:-:b5:14:17,b6:b2:-:-:26:29,b3:b1:-:b2:5:8
cache loopnest 9 0 - -
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
fstate laidout
dcllen 7
zvar v6:1
end
pass 51 "schedule"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b2:0,b3:0 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b5:b2,b7:b2,b6:b2,b3:b1
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b5:b2:-:b6:20:23,b7:b2:-:b5:14:17,b6:b2:-:-:26:29,b3:b1:-:b2:5:8
cache loopnest 9 0 - -
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
fstate scheduled,laidout
dcllen 7
zvar v6:1
end
pass 52 "late nilcheck"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b2:0,b3:0 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b5:b2,b7:b2,b6:b2,b3:b1
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b5:b2:-:b6:20:23,b7:b2:-:b5:14:17,b6:b2:-:-:26:29,b3:b1:-:b2:5:8
cache loopnest 9 0 - -
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
fstate scheduled,laidout
dcllen 7
zvar v6:1
end
pass 53 "flagalloc"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b2:0,b3:0 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v8 Phi t14 0 - p1:1:0:2:0 1 v35,v43
v v9 Phi t19 0 - p1:1:0:2:0 1 v31,v42
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v27,v36,v2,v23,v32,v38,v18,v37,v41,v40,v19,v15,v25,v7,v13,v14,v33,v24,v26,v20,v22,v10
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b5:b2,b7:b2,b6:b2,b3:b1
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b5:b2:-:b6:20:23,b7:b2:-:b5:14:17,b6:b2:-:-:26:29,b3:b1:-:b2:5:8
cache loopnest 9 0 - -
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
fstate scheduled,laidout
dcllen 7
zvar v6:1
end
pass 54 "regalloc"
aux a1 call "AuxCall{regexp/syntax.(*InstOp).String}" a2 1 1 1 8 8 1 2
abiparam in 0 t2 a3 0 0
abiparam out 0 t4 a4 0,1 -1
callreg 0:1,1:2 - 0 -
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b2:0,b3:0 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v27 Copy t14 0 - p1:1:0:2:0 1 v35
v v36 Copy t19 0 - p1:1:0:2:0 1 v31
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v8 Phi t14 0 - p1:1:0:2:0 1 v27,v43
v v9 Phi t19 0 - p1:1:0:2:0 1 v36,v42
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v2,v7,v10,v13,v14,v15,v18,v19,v20,v22,v23,v24,v25,v26,v32,v33,v37,v38,v40,v41
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b5:b2,b7:b2,b6:b2,b3:b1
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b5:b2:-:b6:20:23,b7:b2:-:b5:14:17,b6:b2:-:-:26:29,b3:b1:-:b2:5:8
cache loopnest 9 0 - -
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
fstate scheduled,laidout
regalloc 45 v3:SB,v4:R5,v5:R4,v6:R0,v8:R1,v9:R0,v16:R2,v21:R3,v27:R1,v29:R2,v30:(R0;R1),v31:ZERO,v34:R2,v35:ZERO,v36:R0,v39:[],v42:R0,v43:R1,v44:(R4;R5)
dcllen 7
zvar v6:1
end
pass 55 "loop rotate"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b2:0,b3:0 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v27 Copy t14 0 - p1:1:0:2:0 1 v35
v v36 Copy t19 0 - p1:1:0:2:0 1 v31
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v8 Phi t14 0 - p1:1:0:2:0 1 v27,v43
v v9 Phi t19 0 - p1:1:0:2:0 1 v36,v42
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v2,v7,v10,v13,v14,v15,v18,v19,v20,v22,v23,v24,v25,v26,v32,v33,v37,v38,v40,v41
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b5:b2,b7:b2,b6:b2,b3:b1
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b5:b2:-:b6:20:23,b7:b2:-:b5:14:17,b6:b2:-:-:26:29,b3:b1:-:b2:5:8
cache loopnest 9 0 - -
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
fstate scheduled,laidout
regalloc 45 v3:SB,v4:R5,v5:R4,v6:R0,v8:R1,v9:R0,v16:R2,v21:R3,v27:R1,v29:R2,v30:(R0;R1),v31:ZERO,v34:R2,v35:ZERO,v36:R0,v39:[],v42:R0,v43:R1,v44:(R4;R5)
dcllen 7
zvar v6:1
end
pass 56 "trim"
f b1 t1 a1 44 8
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b2:0,b3:0 -
v v6 ArgIntReg t2 0 a11 p1:1:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
b b2 ARM64UGE p484:56:24:1:0 0 0 - v28 b5:0,b7:0 b1:0
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v16 ARM64MOVBUload t3 0 - p1:1:0:0:0 2 v6,v1
v v21 ARM64MOVDreg t17 0 - p484:56:10:1:0 1 v16
v v44 ARM64LDP t41 0 a6 p484:56:24:1:0 2 v3,v1
v v4 Select1 t14 0 - p484:56:24:1:0 1 v44
v v5 Select0 t36 0 - p484:56:24:1:0 1 v44
v v17 InlMark t32 375 - p1:1:0:0:0 0 v1
v v28 ARM64CMP t31 0 - p484:56:13:1:0 1 v21,v4
b b5 Plain p1:1:0:1:0 0 0 - - b6:0 b2:0
v v35 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v31 ARM64ZERO t19 0 - p0:0:0:0:0 1 -
v v27 Copy t14 0 - p1:1:0:2:0 1 v35
v v36 Copy t19 0 - p1:1:0:2:0 1 v31
b b7 Plain p1:1:0:1:0 0 0 - - b6:1 b2:1
v v29 ARM64MOVDreg t14 0 - p484:59:20:0:0 1 v16
v v34 ARM64ADDshiftLL t36 4 - p484:59:20:1:0 1 v5,v29
v v30 ARM64LDP t42 0 - p484:59:20:0:0 2 v34,v1
v v43 Select1 t14 0 - p484:59:20:0:0 1 v30
v v42 Select0 t19 0 - p484:59:20:0:0 1 v30
b b6 Ret p1:1:0:1:0 0 0 - v39 - b5:0,b7:0
v v8 Phi t14 0 - p1:1:0:2:0 1 v27,v43
v v9 Phi t19 0 - p1:1:0:2:0 1 v36,v42
v v39 MakeResult t40 0 - p1:1:0:0:0 1 v9,v8,v1
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a7 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s4,s5
named s1 v6
named s2 v16
named s4 v31,v42,v9
named s5 v35,v43,v8
splits s3/0/t19=s4,s3/8/t14=s5
canon a3/t2/0/-/0=s1,a9/t3/0/-/0=s2,a10/t4/0/-/0=s3
consts -
freev v2,v7,v10,v13,v14,v15,v18,v19,v20,v22,v23,v24,v25,v26,v32,v33,v37,v38,v40,v41
freeb b4,b8
cache postorder b6,b5,b7,b2,b3,b1
cache idom b1:-,b2:b1,b5:b2,b7:b2,b6:b2,b3:b1
cache sdom b1:-:b3:-:2:35,b2:b1:b7:-:11:32,b5:b2:-:b6:20:23,b7:b2:-:b5:14:17,b6:b2:-:-:26:29,b3:b1:-:b2:5:8
cache loopnest 9 0 - -
cache auxmap -:1,a3:2,a6:3,a11:4
cache linestarts 1:1:1,484:56:59
fstate scheduled,laidout
regalloc 45 v3:SB,v4:R5,v5:R4,v6:R0,v8:R1,v9:R0,v16:R2,v21:R3,v27:R1,v29:R2,v30:(R0;R1),v31:ZERO,v34:R2,v35:ZERO,v36:R0,v39:[],v42:R0,v43:R1,v44:(R4;R5)
dcllen 7
zvar v6:1
end
frontend
end
ptrcache t4,t7,t8,t9,t10,t12,t14,t15,t16,t18,t19,t26,t29,t36,t38
typelink t30=t34
typeorder t6,t10,t3,t7,t11,t8,t12,t9,t13,t14,t17,t18,t27,t28,t15,t16,t5,t19,t2,t20,t21,t22,t23,t24,t25,t26,t35,t37,t36,t1,t38,t4,t29,t30,t32,t31,t33,t42,t41,t34,t39,t40
eof
"#

/-- `std/std/regexp/syntax/%28%2AInstOp%29.String,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "regexp/syntax"
func "(*InstOp).String" 1
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
type t1 8 8 8 1 01 "*InstOp"
name n1 "i" PPARAM t1 1 "regexp/syntax.i" 0 a3
type t2 16 8 8 1 01 "string"
name n2 "~r0" PPARAMOUT t2 1 "regexp/syntax.~r0" 0 a4
type t3 1 1 0 0 - "InstOp"
name n3 "i" PAUTO t3 1 "regexp/syntax.i" 0 a9
name n4 "~r0" PAUTO t2 1 "regexp/syntax.~r0" 0 a10
type t4 8 8 0 0 - "int"
name n5 ".autotmp_4" PAUTO t4 3 "regexp/syntax..autotmp_4" 0 -
type t5 8 8 8 1 01 "*uint8"
name n6 "~r0.ptr" PAUTO t5 3 "regexp/syntax.~r0.ptr" 0 a12
name n7 "~r0.len" PAUTO t4 3 "regexp/syntax.~r0.len" 0 a13
in n1 0 used
in n2 0 outregs
in n3 0 used
in n4 0 -
in n5 0 used,autotmp
in n6 0 used
in n7 0 used
out n1 0 used
opt n2 0 outregs
opt n4 0 -
opt n6 0 -
opt n5 0 autotmp
opt n7 0 -
opt n3 0 -
stack 0 0 8
end
genin
posbase p1 "<autogenerated>" 1 1 -1 0 "<autogenerated>" "<autogenerated>" 1 1
sym y1 "regexp/syntax.(*InstOp).String" 1
curfn p1:1:0:0:0 0 0
regargs 8192:0:t1
text y1 0 0 23 0 1 200091
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "regexp/syntax.(*InstOp).String.arginfo1" 0
sym y5 "regexp/syntax.(*InstOp).String.argliveinfo" 0
sym y6 "regexp/syntax.InstOp.String" 1
inl i375 - p1:1:0:0:0 y6 "InstOp.String"
posbase p484 "regexp/syntax/prog.go" 1 1 375 6 "regexp/syntax/prog.go" "regexp/syntax/prog.go" 1 1
sym y7 "regexp/syntax.instOpNames" 0
sym y8 "runtime.panicwrap" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p1:1:0:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p1:1:0:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p1:1:0:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p1:1:0:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p1:1:0:2:0
p 6 6 0 0 0 - CBZ 0 REG/8192/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@19 0 0 p1:1:0:1:0
p 7 7 0 0 0 - MOVBU 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p1:1:0:2:0
p 8 8 0 0 0 - MOVD 0 REG/8194/0/0/NONE/0/0/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p484:56:10:1:0
p 9 9 0 0 0 - LDP 0 MEM/0/0/0/EXTERN/0/0/y7/- 0 - REGREG/8196/0/0/NONE/0/8197/-/- 0 0 p484:56:24:2:0
p 10 10 0 0 0 - NOP 0 _ 0 - _ 0 0 p0:0:0:0:0
p 11 11 0 0 0 - CMP 0 REG/8197/0/0/NONE/0/0/-/- 8195 - _ 0 0 p484:56:13:2:0
p 12 12 0 0 0 - BLO 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@16 0 0 p484:56:24:2:0
p 13 13 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p1:1:0:1:0
p 14 14 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p1:1:0:2:0
p 15 15 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@18 0 0 p1:1:0:2:0
p 16 16 0 0 0 - ADD 0 SHIFT/0/0/0/NONE/0/135168/-/- 8196 - REG/8194/0/0/NONE/0/0/-/- 0 0 p484:59:20:1:0
p 17 17 0 0 0 - LDP 0 MEM/8194/0/0/NONE/0/0/-/- 0 - REGREG/8192/0/0/NONE/0/8193/-/- 0 0 p484:59:20:2:0
p 18 18 0 0 0 - RET 0 _ 0 - _ 0 0 p1:1:0:1:0
p 19 19 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p1:1:0:2:0
p 20 20 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y8/- 0 0 p1:1:0:2:0
p 21 21 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p1:1:0:0:0
p 22 22 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 23 0 1 200091
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
inlmark @6 375
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgslot 1 n3 t3 0
dbgslot 2 n6 t5 0
dbgslot 3 n7 t4 0
dbgvar 0 n1 0
dbgvar 1 n3 1
dbgloc 0 1:-10000:5:36:50
dbgloc 1 2:16:7:29:52
dbgregout n2
dbgpc 5:36:15,2:16:8,7:29:16
end
asm
sym y9 "runtime.morestack_noctxt" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p1:1:0:0:0
p 23 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 24 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:0:0
p 25 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:0:0
p 26 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@37 0 0 p1:1:0:0:0
p 27 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p1:1:0:0:0
p 28 12 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p1:1:0:0:1
p 29 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p1:1:0:0:0
p 30 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p1:1:0:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p1:1:0:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p1:1:0:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p1:1:0:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p1:1:0:2:0
p 6 24 0 0 85 - CBZ 0 REG/8192/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/19/-/@19 0 0 p1:1:0:1:0
p 7 28 0 0 294 - MOVBU 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p1:1:0:2:0
p 8 32 0 0 301 - MOVD 0 REG/8194/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p484:56:10:1:0
p 31 36 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-3/-/- 0 0 p484:56:10:1:0
p 9 36 0 0 251 - LDP 0 MEM/0/0/0/EXTERN/110/0/y7/- 0 - REGREG/8196/0/0/NONE/7/8197/-/- 0 0 p484:56:24:2:0
p 32 48 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p484:56:24:2:0
p 10 48 0 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p0:0:0:0:0
p 11 48 0 0 92 - CMP 0 REG/8197/0/0/NONE/2/0/-/- 8195 - NONE/0/0/0/NONE/1/0/-/- 0 0 p484:56:13:2:0
p 12 52 0 0 80 - BLO 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/16/-/@16 0 0 p484:56:24:2:0
p 13 56 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 14 60 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p1:1:0:2:0
p 15 64 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/18/-/@18 0 0 p1:1:0:2:0
p 16 68 0 0 27 - ADD 0 SHIFT/0/0/0/NONE/8/135168/-/- 8196 - REG/8194/0/0/NONE/2/0/-/- 0 0 p484:59:20:1:0
p 17 72 0 0 245 - LDP 0 MEM/8194/0/0/NONE/77/0/-/- 0 - REGREG/8192/0/0/NONE/7/8193/-/- 0 0 p484:59:20:2:0
p 18 76 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 33 80 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 34 84 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p1:1:0:1:0
p 19 88 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p1:1:0:2:0
p 20 88 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y8/- 0 0 p1:1:0:2:0
p 21 92 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:0:0
p 35 96 -16 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:0:0
p 36 96 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p1:1:0:0:0
p 37 96 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:0:0
p 38 96 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p1:1:0:0:0
p 39 100 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 40 104 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y9/- 0 0 p1:1:0:0:0
p 41 108 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p1:1:0:0:0
p 42 108 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 43 112 16 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@23 0 0 p1:1:0:0:0
fn y1 8 8 23 0 1 200091
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
inlmark @6 375
funcaux y2 y3 - - y4 y5 -
text 128 0 900b40f9ff6330ebc9020054fe0f1ff8fd831ff8fd2300d1000200b402004039e30302aa1b0000907b030091641740a97f0005eb83000054e1031faae0031faa030000148210028b400440a9fd835ff8fe0741f8c0035fd6000000941f2003d5e00700f9e3031eaa00000094e00740f9e4ffff17000000000000000000000000 3
reloc 36 8 R_ADDRARM64 0 y7
reloc 88 4 R_CALLARM64 0 y8
reloc 104 4 R_CALLARM64 0 y9
pcln y14 y15 y16 y17 y10,y11,y12,y13 y2,y3,_,_,_,y4,y5
usedfiles 0,6
inltree 0 -1 p1:1:0:0:0 y6 "InstOp.String" 24
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y10 SRODATA 15 1 28000 0001010202060303040c0103020500 0
data y11 SRODATA 7 1 28000 00160402030800 0
data y12 SRODATA 0 1 28000 - 0
data y13 SRODATA 5 1 28000 0006041a00 0
data y14 SRODATA 11 1 28000 020420111f0120021f0800 0
data y15 SRODATA 11 1 28000 02080c060b030c020b0d00 0
data y16 SRODATA 11 1 28000 04086e066d037402730d00 0
data y17 SRODATA 11 1 28000 0008020601030202010d00 0
end
dwarf
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
sym y21 "" 0
posbase p7 "regexp/syntax/prog.go" 1 1 -1 6 "regexp/syntax/prog.go" "regexp/syntax/prog.go" 1 1
sym y22 "go:info.regexp/syntax.InstOp.String$abstract" 0
sym y23 "go:info.*regexp/syntax.InstOp" 0
sym y24 "go:info.string" 0
sym y25 "go:info.regexp/syntax.InstOp" 0
sym y26 "type:string" 0
dwfn y18 y19 y20 - y21 "regexp/syntax.(*InstOp).String" 0:1 1 1 1 132
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwinlfn y6 y22
dwinldcl y6 "i" 0 p7:55:7:0:0
dwinldcl y6 "~r0" 0 p7:55:26:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "*regexp/syntax.InstOp" 0 0 1 p7:55:7:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "string" 0 0 1 p7:55:26:0:0
dwname n4 1 0 0 1 0 0 0 0 - - "string" 0 0 1 p484:55:26:0:0
dwname n6 1 0 0 0 0 0 0 0 - - "*uint8" 0 0 1 p484:55:26:0:0
dwname n5 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p484:56:24:0:0
dwname n7 1 0 0 0 0 0 0 0 - - "int" 0 0 1 p484:55:26:0:0
dwname n3 1 0 0 1 0 0 0 0 - - "regexp/syntax.InstOp" 0 0 1 p484:55:7:0:0
var 0 0 "i" 5 1 0 0 0 8 y23 "regexp/syntax/prog.go" 55 7 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y24 "regexp/syntax/prog.go" 55 26 0 1 0 0 -
var 2 0 "i" 5 1 0 1 0 -8 y25 "regexp/syntax/prog.go" 55 7 376 0 1 0 v1
scope 0 0 - 0,1,2
inlcall 0 375 0:1 y22 - 1 32:48,48:56,68:76 2
dieref y18 7 y22 0
data y18 SDWARFFCN 89 0 0 047265676578702f73796e7461782e282a496e73744f70292e537472696e670000008001019c012d6900003700000000000000002e7e7230000137000000000009000000000000000001000000012900000000000000000000 9
reloc 0 0 R_USETYPE 0 y26
reloc 32 2 R_DWTXTADDR_U2 0 y1
reloc 44 4 R_DWARFSECREF 0 y23
reloc 48 4 R_DWARFSECREF 0 y19
reloc 59 4 R_DWARFSECREF 0 y24
reloc 65 4 R_DWARFSECREF 0 y22
reloc 69 4 R_DWARFSECREF 0 y20
reloc 79 4 R_DWARFSECREF 0 y22
reloc 83 4 R_DWARFSECREF 9 y19
data y19 SDWARFLOC 18 0 0 010000040040015000010000042044015200 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
data y20 SDWARFRANGE 13 0 0 01000004203004303804444c00 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y21 SDWARFLINES 54 0 0 00090200000000000000000a8706af04070603323c0637040106034dd306370407060335640637040106034a33068706370224000101 1
reloc 3 8 R_ADDR 0 y1
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

/-- The PC table `checkG35` gives (`b2`: one entry per value `v3`, `v16`, `v21`, `v44`, `v4`, `v5`,
`v17`, `v28`, then the branch). -/
def tab : PcTab :=
  [(1, [5, 5, 5]), (2, [7, 7, 8, 9, 10, 10, 10, 10, 12]), (5, [13, 13, 13, 14, 15]),
    (7, [16, 16, 17, 18, 18, 18]), (6, [18, 18, 18, 18]), (3, [19, 21, 21])]

/-- The class table `checkG35` gives. -/
def kt : KTab := (match checkG35 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 2).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG35`. -/
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

/-- The `runLoc` state before `v4`: the byte `i = 0x2a` (`v16`) in `R2`, its 64-bit copy (`v21`)
in `R3`, the length `7` in `R5`, every other register `poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 2 then .int .w8 0x2a else if i.val = 3 then .int .w64 0x2a
      else if i.val = 5 then .int .w64 7 else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v4`: `X2 = X3 = 0x2a`, zero-extended from 8 bits, `X5 = 7`, the
activation's `g` and `FP`, the PC of `v4`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 2 then 0x2a else if k = 3 then 0x2a else if k = 5 then 7
      else if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 2 4, mem := fun _ => 0 }

/-- The register holds the 64-bit integer `7`. -/
def isW64 : Option Val → Bool
  | some (.int .w64 x) => x == 7
  | _ => false

theorem isW64_spec {o : Option Val} (h : isW64 o = true) : o = some (.int .w64 7) := by
  unfold isW64 at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- The register holds the 8-bit integer `0x2a`. -/
def isW8 : Option Val → Bool
  | some (.int .w8 x) => x == 0x2a
  | _ => false

theorem isW8_spec {o : Option Val} (h : isW8 o = true) : o = some (.int .w8 0x2a) := by
  unfold isW8 at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on `(*InstOp).String`: it holds an arm64 op, `checkG35`
accepts it with `tab` and `kt` and `checkG34` does not; it accesses no frame variable and has no
home slot; `b2` holds `v4` (`Select1 v44`, `v44` an `LDP`) at index 4; `R2`, `R3` and `R5` have
classes 8, 64 and 64 before `v4`, where G35's table is `[(3, 8, false), (2, 8, false)]`; G34's step
`uStep34` empties that table across `v4`, while G35's table after `v4` is still the same;
`stepLoc` runs `v4` from `s0` to `R5 = 7` (64 bits), keeping `R2 = 0x2a` (8 bits). -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG35 lc ps bs g).toOption == some (tab, kt) && (checkG34 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 2 && (lc.ctx.f.block? 2).isSome &&
    (lc.ctx.f.value? 4).isSome && blk.values[4]? == some 4 &&
    (val 4).op == .Select1 && (val 4).args == #[44] && (val 44).op == .ARM64LDP &&
    (kAt lc kt 2 blk 4).get 2 == some 8 && (kAt lc kt 2 blk 4).get 3 == some 64 &&
    (kAt lc kt 2 blk 4).get 5 == some 64 &&
    uL35 lc (uIn35 lc 2) blk 4 == [(3, 8, false), (2, 8, false)] &&
    uStep34 lc (uL35 lc (uIn35 lc 2) blk 4) (val 4) == [] &&
    uL35 lc (uIn35 lc 2) blk 5 == [(3, 8, false), (2, 8, false)] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 4)) fun s1 => isW64 s1.regs[5]? && isW8 s1.regs[2]?

theorem g35_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG35 lc ps bs g = .ok (tab, kt) ∧
      (checkG34 lc ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      2 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 2 = some blk ∧
      lc.ctx.f.value? 4 = some (val 4) ∧ blk.values[4]? = some 4 ∧
      (val 4).op = .Select1 ∧ (val 4).args = #[44] ∧ (val 44).op = .ARM64LDP ∧
      (kAt lc kt 2 blk 4).get 2 = some 8 ∧ (kAt lc kt 2 blk 4).get 3 = some 64 ∧
      (kAt lc kt 2 blk 4).get 5 = some 64 ∧
      uL35 lc (uIn35 lc 2) blk 4 = [(3, 8, false), (2, 8, false)] ∧
      uStep34 lc (uL35 lc (uIn35 lc 2) blk 4) (val 4) = [] ∧
      uL35 lc (uIn35 lc 2) blk 5 = [(3, 8, false), (2, 8, false)] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 4))
        (fun s1 => isW64 s1.regs[5]? && isW8 s1.regs[2]?) = true := by
  have hf := g35_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h34, hav, hsl, hm2, hbs, hvs, hi4, hop, hargs, hop44, hk2, hk3, hk5, hu4,
    hu34, hu5, hrun⟩ := hf
  refine ⟨hl, ?_, h34, hav, hsl, hm2, ?_, ?_, hi4, hop, hargs, hop44, hk2, hk3, hk5, hu4, hu34,
    hu5, hrun⟩
  · revert hres; cases checkG35 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g35Env (hc : checkG35 lc ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ := checkG35_spec hl hc
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ := checkG35_spec hl hc
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

/-! ## `v4`: `Select1 v44`, no code -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 2 ∧ x = .int .w8 0x2a) ∨ (r = 3 ∧ x = .int .w64 0x2a) ∨ (r = 5 ∧ x = .int .w64 7) ∨
      x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · split at h
      · rename_i h1; exact Or.inr (Or.inl ⟨h1, h.symm⟩)
      · split at h
        · rename_i h1; exact Or.inr (Or.inr (Or.inl ⟨h1, h.symm⟩))
        · exact Or.inr (Or.inr (Or.inr h.symm))
  · cases h

theorem locMatch0 : LocMatch E s0 2 4 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show BitVec.setWidth 8 (m0.x 2) = 0x2a
      decide
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl (show m0.x 3 = 0x2a by decide)
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl (show m0.x 5 = 7 by decide)
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g35Inv0 (h2 : (kAt lc kt 2 blk 4).get 2 = some 8) (h3 : (kAt lc kt 2 blk 4).get 3 = some 64)
    (h5 : (kAt lc kt 2 blk 4).get 5 = some 64) :
    G3Inv E lc (kAt lc kt 2 blk 4) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h2] at hc; cases hc; rfl
    · rw [h3] at hc; cases hc; rfl
    · rw [h5] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- `m0` keeps G35's table before `v4`: `X3` and `X2` are zero-extended from 8 bits. -/
theorem uokl0 : UOKL m0 [(3, 8, false), (2, 8, false)] := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · show ∀ k : Nat, k < 31 → objX? 3 = some (BitVec.ofNat 5 k) →
      ExtOK (m0.x (BitVec.ofNat 5 k)) 8 false
    unfold ExtOK
    decide
  · show ∀ k : Nat, k < 31 → objX? 2 = some (BitVec.ofNat 5 k) →
      ExtOK (m0.x (BitVec.ofNat 5 k)) 8 false
    unfold ExtOK
    decide

/-- The per-value premises of `v4`, `Select1`: none apply. -/
theorem pre4 {s : LocState} (hop : (val 4).op = .Select1) : G14Pre lc s (val 4) := by
  have hne : ∀ o : Op, o ≠ .Select1 → (val 4).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G35 on `regexp/syntax.(*InstOp).String`**: before `v4` (`Select1` of the pair load `v44`,
the length of `instOpNames`) G35's table is `[(3, 8, false), (2, 8, false)]`. From the state with
the byte `i = 0x2a` in `R2` and the length `7` in `R5`, on a machine whose `X2` and `X3` are
zero-extended from 8 bits, `g35_value` runs `v4` (no code): `runLoc`'s `R5` holds `7` and `R2`
still the byte `0x2a`, and the machine state, related to it before `v5` under an activation
extending `E` that is again a `G28Env`, has G35's table after `v4` still `[(3, 8, false),
(2, 8, false)]`, which gives the whole `X2 = 0x2a`. G34's step empties the table across `v4` (so
`checkG34` rejects the function). -/
theorem genG35_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 4) = .ok s1 ∧
      s1.regs[5]? = some (.int .w64 7) ∧ s1.regs[2]? = some (.int .w8 0x2a) ∧
      (checkG34 lc ps bs g).toOption = none ∧
      uStep34 lc (uL35 lc (uIn35 lc 2) blk 4) (val 4) = [] ∧
      uL35 lc (uIn35 lc 2) blk 5 = [(3, 8, false), (2, 8, false)] ∧
      E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E1 s1 2 5 m1 ∧ UOKL m1 (uL35 lc (uIn35 lc 2) blk 5) ∧ m1.x 2 = 0x2a := by
  obtain ⟨hl, hc, h34, hav, hsl, hm2, hb, hv4, hi4, hop, -, -, hk2, hk3, hk5, hu4, hu34, hu5,
    hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hr
  have hr5 := isW64_spec hr.1
  have hr2 := isW8_spec hr.2
  have hE := g35Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .Select1 → (val 4).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, hu1'⟩ := g35_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm2 hb hi4 hv4 (by rw [hop]; rfl) locMatch0 (g35Inv0 hk2 hk3 hk5)
    (by rw [hu4]; exact uokl0) (pre4 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  have hext : ExtOK (m1.x 2) 8 false := by
    have h := hu1'
    rw [hu5] at h
    exact h (2, 8, false) (by simp) 2 (by decide) rfl
  have hlo : (m1.x 2).setWidth 8 = 0x2a := (hm1'.regs 2 _ hr2).1 2 rfl
  have hx2 : m1.x 2 = 0x2a := by
    simp only [ExtOK, Bool.false_eq_true, ↓reduceIte] at hext
    rw [hext, hlo]
    decide
  exact ⟨s1, E1, m1, hs1, hr5, hr2, h34, hu34, hu5, hx1, hE1, hp1, hm1', hu1', hx2⟩

end GoFV.Proof.Witness.GenG35
