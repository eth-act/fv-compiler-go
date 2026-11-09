import GoFV.Proof.Gen.G39
import GoFV.Proof.Witness.GenG13

/-!
# Non-vacuity witness: slice G39 of the genssa validator on `strings.HasSuffix`

`std/std/strings/HasSuffix,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`;
`strings/strings.go`):

```go
func HasSuffix(s, suffix string) bool {
	return len(s) >= len(suffix) && s[len(s)-len(suffix):] == suffix
}
```

`regalloc` homed `v47` in `R0`; after `trim` its ID is no value of the function, and the export
keeps its home, of shape `Ty.other`, so `checkG38` rejects the function (`v47: register value of
shape Ty.other`). Every value refers to values of the function (`refsLive`), and `checkG39`
accepts it: `checkG38` on `lc = liveCtx lc0`, which drops that home, with the PC table `tab` and
the class table `kt`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g39_facts`),
`stepLoc` runs `v34 = ADD v17 v26` (the first value of `b4`) from a state with `len(s) = 5` in
`R1` and `len(suffix) = 2` in `R3` to `R4 = 7`; it runs alike under `lc0` (`stepLoc_live`). On a
framed activation with `G28Env`, `g39_value` runs it (`genG39_witness`): the machine's `X4` is 7.
-/

namespace GoFV.Proof.Witness.GenG39

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/strings/HasSuffix,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "strings"
func "HasSuffix" 1 0 0
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
config localpkg "strings"
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
type t2 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t1 FUNC 8 8 8 hasptr,direct "func(string, string) bool" "func(string, string) bool" 0 2 1
field 0 "s" t2 ? 0
field 1 "suffix" t2 ? 0
field 2 "" t3 ? 0
aux a2 sym "strings.HasSuffix" "strings.HasSuffix" 1 - 0 - - - - 0
posbase p2 "strings/strings.go" 1 1 -1
aux a3 name "s" "s" PPARAM t2 0 1 used p2:506:16:0:0
aux a4 name "suffix" "suffix" PPARAM t2 16 1 used p2:506:19:0:0
aux a5 name "~r0" "~r0" PPARAMOUT t3 0 1 - p2:506:34:0:0
aux a1 call "AuxCall{strings.HasSuffix}" a2 1 2 1 8 32 4 1
abiparam in 0 t2 a3 0,1 0
abiparam in 1 t2 a4 2,3 16
abiparam out 0 t3 a5 0 -1
type t4 INT8 1 1 0 comparable,named "int8" "int8"
type t5 INT16 2 2 0 comparable,named "int16" "int16"
type t6 INT32 4 4 0 comparable,named "int32" "int32"
type t7 INT64 8 8 0 comparable,named "int64" "int64"
type t8 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t9 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t10 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t11 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t12 INT 8 8 0 comparable,named "int" "int"
type t13 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t14 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t15 UINT 8 8 0 comparable,named "uint" "uint"
type t16 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t12
type t21 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t16
type t22 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t13
type t23 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t14
type t24 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t17
type t25 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t26 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t27 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t28 SSA ? ? ? - "mem" ""
type t29 SSA ? ? ? - "flags" ""
type t30 SSA ? ? ? - "void" ""
type t31 SSA 16 8 ? - "int128" ""
type t32 RESULTS ? ? ? - "mem" "" 1 t28
posbase p161 "internal/stringslite/strings.go" 1 1 91
type t33 PTR 8 8 8 hasptr,direct,comparable "*string" "*string" t2
type t34 PTR 8 8 8 hasptr,direct,comparable "*bool" "*bool" t3
type t35 RESULTS ? ? ? - "bool,mem" "" 2 t3,t28
slot s1 a3 t2 0 - 0
slot s2 a4 t2 0 - 0
aux a6 name "stringslite.s" "s" PAUTO t2 0 1 used p161:20:16:0:0
slot s3 a6 t2 0 - 0
aux a7 name "stringslite.suffix" "suffix" PAUTO t2 0 1 used p161:20:19:0:0
slot s4 a7 t2 0 - 0
aux a8 name "~r0" "~r0" PAUTO t3 0 1 - p161:20:34:0:0
slot s5 a8 t3 0 - 0
f b1 t1 a1 53 8
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t14,UInt=t15,Uintptr=t16,String=t2,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t34 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p2:506:6:2:0 2 -
v v8 Arg t2 0 a4 p2:506:6:2:0 2 -
v v9 ConstBool t3 0 - p0:0:0:0:0 0 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:0:0 1 v7
v v12 StringLen t12 0 - p161:21:22:0:0 1 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 2 v12,v11
v v25 Const64 t12 1 - p0:0:0:0:0 1 -
b b2 Plain p2:507:30:1:0 0 0 - - b8:0 b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:0:0 1 v13,v47
v v52 Phi t28 0 - p2:507:30:0:0 1 v1,v53
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 Copy t2 0 - p161:21:39:2:0 3 v7
v v15 StringLen t12 0 - p161:21:39:0:0 1 v14
v v16 Copy t2 0 - p161:21:46:2:0 2 v8
v v17 StringLen t12 0 - p161:21:46:0:0 1 v16
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v15,v17
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v14
v v20 StringLen t12 0 - p161:21:35:0:0 3 v14
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v20
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v20,v18
v v26 Mul64 t12 0 - p161:21:35:0:0 1 v18,v25
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v26,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 2 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 1 v30
v v32 Copy t16 0 - p161:21:57:2:0 1 v31
v v33 Copy t2 0 - p161:21:57:2:0 2 v16
v v34 StringLen t12 0 - p161:21:57:0:0 1 v33
v v35 Copy t16 0 - p161:21:57:2:0 1 v34
v v36 Eq64 t3 0 - p161:21:57:0:0 2 v32,v35
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v22 Copy t28 0 - p161:21:35:2:0 1 v1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v20,v22
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v37 Copy t2 0 - p161:21:57:2:0 2 v30
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v37
v v39 Copy t27 0 - p161:21:57:2:0 1 v38
v v40 Copy t2 0 - p161:21:57:2:0 1 v33
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v40
v v42 Copy t27 0 - p161:21:57:2:0 1 v41
v v43 StringLen t12 0 - p161:21:57:0:0 1 v37
v v44 Copy t16 0 - p161:21:57:2:0 1 v43
v v45 Copy t28 0 - p161:21:57:2:0 2 v1
v v46 MemEq t3 0 - p161:21:57:0:0 1 v39,v42,v44,v45
b b7 Plain p161:21:57:0:0 0 0 - - b2:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v36,v46
v v53 Phi t28 0 - p161:21:57:0:0 1 v1,v45
b b8 Ret p2:507:2:1:0 0 0 - v51 - b2:0
v v49 Copy t3 0 - p2:507:2:2:0 1 v48
v v50 Copy t28 0 - p2:507:2:2:0 1 v52
v v51 MakeResult t35 0 - p2:507:2:0:0 1 v49,v50
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7,v14
named s4 v8,v16,v33,v40
named s5 v48,v49
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v9,1=v25
freev -
freeb -
dcllen 13
end
pass 1 "number lines"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t34 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p2:506:6:2:0 2 -
v v8 Arg t2 0 a4 p2:506:6:2:0 2 -
v v9 ConstBool t3 0 - p0:0:0:0:0 0 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 1 v7
v v12 StringLen t12 0 - p161:21:22:0:0 1 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 2 v12,v11
v v25 Const64 t12 1 - p0:0:0:0:0 1 -
b b2 Plain p2:507:30:1:0 0 0 - - b8:0 b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v13,v47
v v52 Phi t28 0 - p2:507:30:0:0 1 v1,v53
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 Copy t2 0 - p161:21:39:2:0 3 v7
v v15 StringLen t12 0 - p161:21:39:0:0 1 v14
v v16 Copy t2 0 - p161:21:46:2:0 2 v8
v v17 StringLen t12 0 - p161:21:46:0:0 1 v16
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v15,v17
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v14
v v20 StringLen t12 0 - p161:21:35:0:0 3 v14
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v20
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v20,v18
v v26 Mul64 t12 0 - p161:21:35:0:0 1 v18,v25
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v26,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 2 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 1 v30
v v32 Copy t16 0 - p161:21:57:2:0 1 v31
v v33 Copy t2 0 - p161:21:57:2:0 2 v16
v v34 StringLen t12 0 - p161:21:57:0:0 1 v33
v v35 Copy t16 0 - p161:21:57:2:0 1 v34
v v36 Eq64 t3 0 - p161:21:57:0:0 2 v32,v35
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v22 Copy t28 0 - p161:21:35:2:0 1 v1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v20,v22
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v37 Copy t2 0 - p161:21:57:2:0 2 v30
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v37
v v39 Copy t27 0 - p161:21:57:2:0 1 v38
v v40 Copy t2 0 - p161:21:57:2:0 1 v33
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v40
v v42 Copy t27 0 - p161:21:57:2:0 1 v41
v v43 StringLen t12 0 - p161:21:57:0:0 1 v37
v v44 Copy t16 0 - p161:21:57:2:0 1 v43
v v45 Copy t28 0 - p161:21:57:2:0 2 v1
v v46 MemEq t3 0 - p161:21:57:0:0 1 v39,v42,v44,v45
b b7 Plain p161:21:57:0:0 0 0 - - b2:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v36,v46
v v53 Phi t28 0 - p161:21:57:0:0 1 v1,v45
b b8 Ret p2:507:2:1:0 0 0 - v51 - b2:0
v v49 Copy t3 0 - p2:507:2:2:0 1 v48
v v50 Copy t28 0 - p2:507:2:2:0 1 v52
v v51 MakeResult t35 0 - p2:507:2:0:0 1 v49,v50
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7,v14
named s4 v8,v16,v33,v40
named s5 v48,v49
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v9,1=v25
freev -
freeb -
cache postorder b8,b2,b7,b6,b4,b5,b3,b1
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 12 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t34 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p2:506:6:2:0 5 -
v v8 Arg t2 0 a4 p2:506:6:2:0 7 -
v v9 ConstBool t3 0 - p0:0:0:0:0 0 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 1 v7
v v12 StringLen t12 0 - p161:21:22:0:0 1 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 2 v12,v11
v v25 Const64 t12 1 - p0:0:0:0:0 1 -
b b2 Plain p2:507:30:1:0 0 0 - - b8:0 b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 2 v13,v47
v v52 Copy t28 0 - p2:507:30:0:0 0 v1
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v14 Copy t2 0 - p161:21:39:2:0 0 v7
v v15 StringLen t12 0 - p161:21:39:0:0 1 v7
v v16 Copy t2 0 - p161:21:46:2:0 0 v8
v v17 StringLen t12 0 - p161:21:46:0:0 1 v8
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v15,v17
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v20 StringLen t12 0 - p161:21:35:0:0 3 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v20
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v20,v18
v v26 Mul64 t12 0 - p161:21:35:0:0 1 v18,v25
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v26,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 4 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 2 v30
v v32 Copy t16 0 - p161:21:57:2:0 0 v31
v v33 Copy t2 0 - p161:21:57:2:0 0 v8
v v34 StringLen t12 0 - p161:21:57:0:0 2 v8
v v35 Copy t16 0 - p161:21:57:2:0 0 v34
v v36 Eq64 t3 0 - p161:21:57:0:0 2 v31,v34
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v22 Copy t28 0 - p161:21:35:2:0 0 v1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v20,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v37 Copy t2 0 - p161:21:57:2:0 0 v30
v v38 StringPtr t17 0 - p161:21:57:0:0 2 v30
v v39 Copy t27 0 - p161:21:57:2:0 0 v38
v v40 Copy t2 0 - p161:21:57:2:0 0 v8
v v41 StringPtr t17 0 - p161:21:57:0:0 2 v8
v v42 Copy t27 0 - p161:21:57:2:0 0 v41
v v43 StringLen t12 0 - p161:21:57:0:0 2 v30
v v44 Copy t16 0 - p161:21:57:2:0 0 v43
v v45 Copy t28 0 - p161:21:57:2:0 0 v1
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v43,v1
b b7 Plain p161:21:57:0:0 0 0 - - b2:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v36,v46
v v53 Copy t28 0 - p161:21:57:0:0 0 v1
b b8 Ret p2:507:2:1:0 0 0 - v51 - b2:0
v v49 Copy t3 0 - p2:507:2:2:0 0 v48
v v50 Copy t28 0 - p2:507:2:2:0 0 v1
v v51 MakeResult t35 0 - p2:507:2:0:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7,v7
named s4 v8,v8,v8,v8
named s5 v48,v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v9,1=v25
freev -
freeb -
cache postorder b8,b2,b7,b6,b4,b5,b3,b1
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 3 "early deadcode"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 4 -
v v8 Arg t2 0 a4 p2:506:6:2:0 4 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 1 v7
v v12 StringLen t12 0 - p161:21:22:0:0 1 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 2 v12,v11
v v25 Const64 t12 1 - p0:0:0:0:0 1 -
b b2 Plain p2:507:30:1:0 0 0 - - b8:0 b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v13,v47
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v15 StringLen t12 0 - p161:21:39:0:0 1 v7
v v17 StringLen t12 0 - p161:21:46:0:0 1 v8
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v15,v17
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v20 StringLen t12 0 - p161:21:35:0:0 3 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v20
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v20,v18
v v26 Mul64 t12 0 - p161:21:35:0:0 1 v18,v25
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v26,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 3 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 1 v30
v v34 StringLen t12 0 - p161:21:57:0:0 1 v8
v v36 Eq64 t3 0 - p161:21:57:0:0 2 v31,v34
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v20,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v43 StringLen t12 0 - p161:21:57:0:0 1 v30
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v43,v1
b b7 Plain p161:21:57:0:0 0 0 - - b2:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v36,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b2:0
v v51 MakeResult t35 0 - p2:507:2:0:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 1=v25
freev v50,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b8,b2,b7,b6,b4,b5,b3,b1
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 4 "short circuit"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 4 -
v v8 Arg t2 0 a4 p2:506:6:2:0 4 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 1 v7
v v12 StringLen t12 0 - p161:21:22:0:0 1 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
v v25 Const64 t12 1 - p0:0:0:0:0 1 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
b b2 BlockInvalid p2:507:30:1:0 0 0 - - - -
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v15 StringLen t12 0 - p161:21:39:0:0 1 v7
v v17 StringLen t12 0 - p161:21:46:0:0 1 v8
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v15,v17
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v20 StringLen t12 0 - p161:21:35:0:0 3 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v20
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v20,v18
v v26 Mul64 t12 0 - p161:21:35:0:0 1 v18,v25
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v26,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 3 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 1 v30
v v34 StringLen t12 0 - p161:21:57:0:0 1 v8
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v34
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v20,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v43 StringLen t12 0 - p161:21:57:0:0 1 v30
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v43,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50,1=v25
freev v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb -
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 5 "decompose user"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 4 -
v v8 Arg t2 0 a4 p2:506:6:2:0 4 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 1 v7
v v12 StringLen t12 0 - p161:21:22:0:0 1 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
v v25 Const64 t12 1 - p0:0:0:0:0 1 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
b b2 BlockInvalid p2:507:30:1:0 0 0 - - - -
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v15 StringLen t12 0 - p161:21:39:0:0 1 v7
v v17 StringLen t12 0 - p161:21:46:0:0 1 v8
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v15,v17
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v20 StringLen t12 0 - p161:21:35:0:0 3 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v20
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v20,v18
v v26 Mul64 t12 0 - p161:21:35:0:0 1 v18,v25
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v26,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 3 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 1 v30
v v34 StringLen t12 0 - p161:21:57:0:0 1 v8
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v34
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v20,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v43 StringLen t12 0 - p161:21:57:0:0 1 v30
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v43,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50,1=v25
freev v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb -
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 4 -
v v8 Arg t2 0 a4 p2:506:6:2:0 4 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 1 v7
v v12 StringLen t12 0 - p161:21:22:0:0 1 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
v v25 Const64 t12 1 - p0:0:0:0:0 1 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v15 StringLen t12 0 - p161:21:39:0:0 1 v7
v v17 StringLen t12 0 - p161:21:46:0:0 1 v8
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v15,v17
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v20 StringLen t12 0 - p161:21:35:0:0 3 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v20
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v20,v18
v v26 Mul64 t12 0 - p161:21:35:0:0 1 v18,v25
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v26,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 3 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 1 v30
v v34 StringLen t12 0 - p161:21:57:0:0 1 v8
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v34
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v20,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v43 StringLen t12 0 - p161:21:57:0:0 1 v30
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v43,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50,1=v25
freev v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 7 "opt"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 4 -
v v8 Arg t2 0 a4 p2:506:6:2:0 4 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 1 v7
v v12 StringLen t12 0 - p161:21:22:0:0 1 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v15 StringLen t12 0 - p161:21:39:0:0 1 v7
v v17 StringLen t12 0 - p161:21:46:0:0 1 v8
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v15,v17
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v20 StringLen t12 0 - p161:21:35:0:0 3 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v20
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v20,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 3 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 1 v30
v v34 StringLen t12 0 - p161:21:57:0:0 1 v8
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v34
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v20,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v43 StringLen t12 0 - p161:21:57:0:0 1 v30
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v43,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 8 "zero arg cse"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 4 -
v v8 Arg t2 0 a4 p2:506:6:2:0 4 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 1 v7
v v12 StringLen t12 0 - p161:21:22:0:0 1 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v15 StringLen t12 0 - p161:21:39:0:0 1 v7
v v17 StringLen t12 0 - p161:21:46:0:0 1 v8
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v15,v17
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v20 StringLen t12 0 - p161:21:35:0:0 3 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v20
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v20,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 3 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 1 v30
v v34 StringLen t12 0 - p161:21:57:0:0 1 v8
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v34
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v20,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v43 StringLen t12 0 - p161:21:57:0:0 1 v30
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v43,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 9 "opt deadcode"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 4 -
v v8 Arg t2 0 a4 p2:506:6:2:0 4 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 1 v7
v v12 StringLen t12 0 - p161:21:22:0:0 1 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v15 StringLen t12 0 - p161:21:39:0:0 1 v7
v v17 StringLen t12 0 - p161:21:46:0:0 1 v8
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v15,v17
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v20 StringLen t12 0 - p161:21:35:0:0 3 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v20
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v20,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 3 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 1 v30
v v34 StringLen t12 0 - p161:21:57:0:0 1 v8
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v34
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v20,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v43 StringLen t12 0 - p161:21:57:0:0 1 v30
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v43,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 10 "generic cse"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 4 -
v v8 Arg t2 0 a4 p2:506:6:2:0 4 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 5 v7
v v12 StringLen t12 0 - p161:21:22:0:0 3 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v15 StringLen t12 0 - p161:21:39:0:0 0 v7
v v17 StringLen t12 0 - p161:21:46:0:0 0 v8
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v11,v12
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v20 StringLen t12 0 - p161:21:35:0:0 0 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v11
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v11,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 3 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 2 v30
v v34 StringLen t12 0 - p161:21:57:0:0 0 v8
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v12
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v11,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v43 StringLen t12 0 - p161:21:57:0:0 0 v30
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v31,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 11 "phiopt"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 4 -
v v8 Arg t2 0 a4 p2:506:6:2:0 4 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 5 v7
v v12 StringLen t12 0 - p161:21:22:0:0 3 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v15 StringLen t12 0 - p161:21:39:0:0 0 v7
v v17 StringLen t12 0 - p161:21:46:0:0 0 v8
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v11,v12
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v20 StringLen t12 0 - p161:21:35:0:0 0 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v11
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v11,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 3 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 2 v30
v v34 StringLen t12 0 - p161:21:57:0:0 0 v8
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v12
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v11,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v43 StringLen t12 0 - p161:21:57:0:0 0 v30
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v31,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 12 "gcse deadcode"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 2 -
v v8 Arg t2 0 a4 p2:506:6:2:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 5 v7
v v12 StringLen t12 0 - p161:21:22:0:0 3 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v11,v12
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v11
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v11,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 2 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 2 v30
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v12
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v11,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v31,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v43,v34,v20,v17,v15,v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 13 "nilcheckelim"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 2 -
v v8 Arg t2 0 a4 p2:506:6:2:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 5 v7
v v12 StringLen t12 0 - p161:21:22:0:0 3 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
b b3 If p161:21:35:0:0 1 0 - v21 b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v11,v12
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 1 v18,v11
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v11,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 2 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 2 v30
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v12
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v11,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v31,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v43,v34,v20,v17,v15,v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 14 "prove"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 2 -
v v8 Arg t2 0 a4 p2:506:6:2:0 2 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 5 v7
v v12 StringLen t12 0 - p161:21:22:0:0 3 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 4 v11,v12
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
v v21 IsSliceInBounds t3 0 - p161:21:35:0:0 0 v18,v11
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v11,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 2 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 2 v30
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v12
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v11,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v31,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v43,v34,v20,v17,v15,v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 15 "divisible"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 2 -
v v8 Arg t2 0 a4 p2:506:6:2:0 2 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 4 v7
v v12 StringLen t12 0 - p161:21:22:0:0 3 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 3 v11,v12
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v11,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 2 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 2 v30
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v12
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v11,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v31,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v21,v43,v34,v20,v17,v15,v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 16 "divmod"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 2 -
v v8 Arg t2 0 a4 p2:506:6:2:0 2 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 4 v7
v v12 StringLen t12 0 - p161:21:22:0:0 3 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 3 v11,v12
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v11,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 2 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 2 v30
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v12
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v11,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v31,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v21,v43,v34,v20,v17,v15,v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 17 "middle opt"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 2 -
v v8 Arg t2 0 a4 p2:506:6:2:0 2 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 4 v7
v v12 StringLen t12 0 - p161:21:22:0:0 3 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 3 v11,v12
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v11,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 2 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 2 v30
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v12
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v11,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v31,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v21,v43,v34,v20,v17,v15,v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 18 "known bits"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 2 -
v v8 Arg t2 0 a4 p2:506:6:2:0 2 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 4 v7
v v12 StringLen t12 0 - p161:21:22:0:0 3 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 3 v11,v12
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v11,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 2 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 2 v30
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v12
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v11,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v31,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v21,v43,v34,v20,v17,v15,v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 19 "early fuse"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p2:506:6:2:0 2 -
v v8 Arg t2 0 a4 p2:506:6:2:0 2 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 4 v7
v v12 StringLen t12 0 - p161:21:22:0:0 3 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 3 v11,v12
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v11,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 2 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 2 v30
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v12
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v11,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v31,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v21,v43,v34,v20,v17,v15,v26,v25,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 20 "expand calls"
aux a9 nameoff "s+0" a3 0
aux a10 nameoff "s+8" a3 8
aux a11 nameoff "suffix+0" a4 0
aux a12 nameoff "suffix+8" a4 8
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 StringMake t2 0 - p161:21:31:2:0 2 v20,v17
v v8 StringMake t2 0 - p161:21:31:2:0 2 v15,v26
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v11 StringLen t12 0 - p161:21:12:1:0 4 v7
v v12 StringLen t12 0 - p161:21:22:0:0 3 v8
v v13 Leq64 t3 0 - p161:21:16:0:0 1 v12,v11
v v21 SB t16 0 - p0:0:0:0:0 0 -
v v43 SP t16 0 - p0:0:0:0:0 2 -
v v34 OffPtr t33 0 - p0:0:0:0:0 0 v43
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 1 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 1 -
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 3 v11,v12
v v19 StringPtr t17 0 - p161:21:35:0:0 1 v7
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 2 v11,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v19,v28
v v30 StringMake t2 0 - p161:21:35:0:0 2 v29,v24
v v31 StringLen t12 0 - p161:21:57:0:0 2 v30
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v31,v12
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v11,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v38 StringPtr t17 0 - p161:21:57:0:0 1 v30
v v41 StringPtr t17 0 - p161:21:57:0:0 1 v8
v v46 MemEq t3 0 - p161:21:57:0:0 1 v38,v41,v31,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
v v25 LocalAddr t34 0 a5 p2:507:2:1:0 0 v43,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v8
named s5 v48
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50,v34
freev v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 13
end
pass 21 "decompose builtin"
slot s6 a3 t17 0 - 0
slot s7 a3 t12 8 - 0
slot s8 a4 t17 0 - 0
slot s9 a4 t12 8 - 0
aux a13 name "s.ptr" "s.ptr" PAUTO t17 0 3 used p161:20:16:0:0
slot s10 a13 t17 0 s3 0
aux a14 name "s.len" "s.len" PAUTO t12 0 3 used p161:20:16:0:0
slot s11 a14 t12 0 s3 8
aux a15 name "suffix.ptr" "suffix.ptr" PAUTO t17 0 3 used p161:20:19:0:0
slot s12 a15 t17 0 s4 0
aux a16 name "suffix.len" "suffix.len" PAUTO t12 0 3 used p161:20:19:0:0
slot s13 a16 t12 0 s4 8
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 StringMake t2 0 - p161:21:31:2:0 0 v20,v17
v v8 StringMake t2 0 - p161:21:31:2:0 0 v15,v26
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v13 Leq64 t3 0 - p161:21:16:1:0 1 v26,v17
v v21 SB t16 0 - p0:0:0:0:0 0 -
v v43 SP t16 0 - p0:0:0:0:0 2 -
v v34 OffPtr t33 0 - p0:0:0:0:0 0 v43
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 2 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 2 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 3 v17,v26
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 4 v17,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 2 v20,v28
v v30 StringMake t2 0 - p161:21:35:0:0 0 v29,v24
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v24,v26
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v17,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 MemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
v v25 LocalAddr t34 0 a5 p2:507:2:1:0 0 v43,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50,v34
freev v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 22 "softfloat"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 StringMake t2 0 - p161:21:31:2:0 0 v20,v17
v v8 StringMake t2 0 - p161:21:31:2:0 0 v15,v26
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v13 Leq64 t3 0 - p161:21:16:1:0 1 v26,v17
v v21 SB t16 0 - p0:0:0:0:0 0 -
v v43 SP t16 0 - p0:0:0:0:0 2 -
v v34 OffPtr t33 0 - p0:0:0:0:0 0 v43
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 2 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 2 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 3 v17,v26
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 4 v17,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 2 v20,v28
v v30 StringMake t2 0 - p161:21:35:0:0 0 v29,v24
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v24,v26
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v17,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 MemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
v v25 LocalAddr t34 0 a5 p2:507:2:1:0 0 v43,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50,v34
freev v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 23 "branchelim"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 StringMake t2 0 - p161:21:31:2:0 0 v20,v17
v v8 StringMake t2 0 - p161:21:31:2:0 0 v15,v26
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v13 Leq64 t3 0 - p161:21:16:1:0 1 v26,v17
v v21 SB t16 0 - p0:0:0:0:0 0 -
v v43 SP t16 0 - p0:0:0:0:0 2 -
v v34 OffPtr t33 0 - p0:0:0:0:0 0 v43
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 2 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 2 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 3 v17,v26
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 4 v17,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 2 v20,v28
v v30 StringMake t2 0 - p161:21:35:0:0 0 v29,v24
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v24,v26
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v17,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 MemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
v v25 LocalAddr t34 0 a5 p2:507:2:1:0 0 v43,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50,v34
freev v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 24 "late opt"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v13 Leq64 t3 0 - p161:21:16:1:0 1 v26,v17
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 4 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 3 -
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 3 v17,v26
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 3 v17,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v20,v28
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v24,v26
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v17,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 MemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v25,v30,v34,v43,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 25 "dead auto elim"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v13 Leq64 t3 0 - p161:21:16:1:0 1 v26,v17
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 4 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 3 -
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 3 v17,v26
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 3 v17,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v20,v28
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v24,v26
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v17,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 MemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v25,v30,v34,v43,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 26 "sccp"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v13 Leq64 t3 0 - p161:21:16:1:0 1 v26,v17
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 4 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 3 -
b b3 First p161:21:35:0:0 1 0 - - b4:0,b5:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 3 v17,v26
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 3 v17,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v20,v28
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v24,v26
b b5 Exit p161:21:35:0:0 0 0 - v23 - b3:1
v v23 PanicBounds t28 6 - p161:21:35:0:0 1 v18,v17,v1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 MemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v25,v30,v34,v43,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b4,b5,b3,b1
cache idom b1:-,b3:b1,b4:b3,b5:b3,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b3:-:2:41,b3:b1:b5:b8:5:32,b4:b3:b6:-:14:29,b5:b3:-:b4:8:11,b6:b4:-:b7:17:20,b7:b4:-:-:23:26,b8:b1:-:-:35:38
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 27 "generic deadcode"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b3:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v13 Leq64 t3 0 - p161:21:16:1:0 1 v26,v17
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 3 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 3 -
b b3 Plain p161:21:35:0:0 0 0 - - b4:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 2 v17,v26
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b3:0
v v24 Sub64 t12 0 - p161:21:35:0:0 3 v17,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v20,v28
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v24,v26
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 MemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v23,v25,v30,v34,v43,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b5,b2
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 28 "late fuse"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v13 Leq64 t3 0 - p161:21:16:1:0 1 v26,v17
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 3 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 3 -
b b3 BlockInvalid p161:21:35:0:0 0 0 - - - -
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 2 v17,v26
v v24 Sub64 t12 0 - p161:21:35:0:0 3 v17,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v20,v28
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v24,v26
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 MemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v23,v25,v30,v34,v43,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b5,b2
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 29 "check bce"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v13 Leq64 t3 0 - p161:21:16:1:0 1 v26,v17
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 3 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 3 -
b b3 BlockInvalid p161:21:35:0:0 0 0 - - - -
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 2 v17,v26
v v24 Sub64 t12 0 - p161:21:35:0:0 3 v17,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v20,v28
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v24,v26
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 MemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v23,v25,v30,v34,v43,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b5,b2
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 30 "dse"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v13 Leq64 t3 0 - p161:21:16:1:0 1 v26,v17
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 3 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 3 -
b b3 BlockInvalid p161:21:35:0:0 0 0 - - - -
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 2 v17,v26
v v24 Sub64 t12 0 - p161:21:35:0:0 3 v17,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v20,v28
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v24,v26
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 MemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v23,v25,v30,v34,v43,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b5,b2
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 31 "memcombine"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v13 Leq64 t3 0 - p161:21:16:1:0 1 v26,v17
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 3 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 3 -
b b3 BlockInvalid p161:21:35:0:0 0 0 - - - -
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 2 v17,v26
v v24 Sub64 t12 0 - p161:21:35:0:0 3 v17,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v20,v28
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v24,v26
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 MemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v23,v25,v30,v34,v43,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b5,b2
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 32 "writebarrier"
f b1 t1 a1 53 8
b b1 If p161:21:31:0:0 0 0 - v13 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ConstBool t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v13 Leq64 t3 0 - p161:21:16:1:0 1 v26,v17
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 3 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 3 -
b b3 BlockInvalid p161:21:35:0:0 0 0 - - - -
b b4 If p161:21:57:0:0 0 0 - v36 b6:0,b7:0 b1:0
v v18 Sub64 t12 0 - p161:21:42:0:0 2 v17,v26
v v24 Sub64 t12 0 - p161:21:35:0:0 3 v17,v18
v v27 Slicemask t12 0 - p161:21:35:0:0 1 v24
v v28 And64 t12 0 - p161:21:35:0:0 1 v18,v27
v v29 AddPtr t17 0 - p161:21:35:0:0 1 v20,v28
v v36 Eq64 t3 0 - p161:21:57:0:0 1 v24,v26
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 MemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v50
freev v23,v25,v30,v34,v43,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b5,b2
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 33 "lower"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64MOVDconst t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b3 BlockInvalid p161:21:35:0:0 0 0 - - - -
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b5,b2
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 34 "addressing modes"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64MOVDconst t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b3 BlockInvalid p161:21:35:0:0 0 0 - - - -
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b5,b2
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 35 "late lower"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b3 BlockInvalid p161:21:35:0:0 0 0 - - - -
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b5,b2
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 36 "pair"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b3 BlockInvalid p161:21:35:0:0 0 0 - - - -
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b5,b2
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b3,b5,b2
cache auxmap a3:1,a4:2,-:3
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 38 "lowered cse"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b3,b5,b2
cache postorder b8,b7,b6,b4,b1
cache idom b1:-,b4:b1,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b4:-:2:29,b4:b1:b6:b8:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b1:-:-:23:26
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 39 "elim unread autos"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b3,b5,b2
cache postorder b8,b7,b6,b4,b1
cache idom b1:-,b4:b1,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b4:-:2:29,b4:b1:b6:b8:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b1:-:-:23:26
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b3,b5,b2
cache postorder b8,b7,b6,b4,b1
cache idom b1:-,b4:b1,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b4:-:2:29,b4:b1:b6:b8:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b1:-:-:23:26
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 41 "lowered deadcode"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b3,b5,b2
cache postorder b8,b7,b6,b4,b1
cache idom b1:-,b4:b1,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b4:-:2:29,b4:b1:b6:b8:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b1:-:-:23:26
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 42 "checkLower"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b3,b5,b2
cache postorder b8,b7,b6,b4,b1
cache idom b1:-,b4:b1,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b4:-:2:29,b4:b1:b6:b8:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b1:-:-:23:26
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 43 "loop invariant"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b3,b5,b2
cache postorder b8,b7,b6,b4,b1
cache idom b1:-,b4:b1,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b4:-:2:29,b4:b1:b6:b8:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b1:-:-:23:26
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b3,b5,b2
cache postorder b8,b7,b6,b4,b1
cache idom b1:-,b4:b1,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b4:-:2:29,b4:b1:b6:b8:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b1:-:-:23:26
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 45 "tighten"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b3,b5,b2
cache postorder b8,b7,b6,b4,b1
cache idom b1:-,b4:b1,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b4:-:2:29,b4:b1:b6:b8:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b1:-:-:23:26
cache loopnest 9 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 46 "late deadcode"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b8:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b7:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b1:1,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b3,b5,b2
cache postorder b8,b7,b6,b4,b1
cache idom b1:-,b4:b1,b6:b4,b7:b4,b8:b1
cache sdom b1:-:b4:-:2:29,b4:b1:b6:b8:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b1:-:-:23:26
cache loopnest 9 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 47 "critical"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b3:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b3:0,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b5:0,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
b b3 Plain p161:21:57:0:0 0 0 - - b7:0 b4:1
b b5 Plain p161:21:31:0:0 0 0 - - b8:0 b1:1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 48 "phi tighten"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 0 0 - v43 b6:0,b3:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b3:0,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b5:0,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
b b3 Plain p161:21:57:0:0 0 0 - - b7:0 b4:1
b b5 Plain p161:21:31:0:0 0 0 - - b8:0 b1:1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 49 "likelyadjust"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 -1 0 - v43 b6:0,b3:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b3:0,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b8 Ret p2:507:2:1:0 0 0 - v51 - b5:0,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
b b3 Plain p161:21:57:0:0 0 0 - - b7:0 b4:1
b b5 Plain p161:21:31:0:0 0 0 - - b8:0 b1:1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b3,b4,b5,b1
cache idom b1:-,b4:b1,b6:b4,b7:b4,b8:b1,b3:b4,b5:b1
cache sdom b1:-:b5:-:2:41,b4:b1:b3:b8:11:32,b6:b4:-:b7:20:23,b7:b4:-:-:26:29,b8:b1:-:-:35:38,b3:b4:-:b6:14:17,b5:b1:-:b4:5:8
cache loopnest 9 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
dcllen 17
end
pass 50 "layout"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 -1 0 - v43 b6:0,b3:0 b1:0
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b3 Plain p161:21:57:0:0 0 0 - - b7:0 b4:1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b3:0,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b5 Plain p161:21:31:0:0 0 0 - - b8:0 b1:1
b b8 Ret p2:507:2:1:0 0 0 - v51 - b5:0,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b3,b4,b5,b1
cache idom b1:-,b4:b1,b3:b4,b6:b4,b7:b4,b5:b1,b8:b1
cache sdom b1:-:b5:-:2:41,b4:b1:b3:b8:11:32,b3:b4:-:b6:14:17,b6:b4:-:b7:20:23,b7:b4:-:-:26:29,b5:b1:-:b4:5:8,b8:b1:-:-:35:38
cache loopnest 9 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
fstate laidout
dcllen 17
end
pass 51 "schedule"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b5:0 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 -1 0 - v43 b6:0,b3:0 b1:0
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b3 Plain p161:21:57:0:0 0 0 - - b7:0 b4:1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b3:0,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b5 Plain p161:21:31:0:0 0 0 - - b8:0 b1:1
b b8 Ret p2:507:2:1:0 0 0 - v51 - b5:0,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b3,b4,b5,b1
cache idom b1:-,b4:b1,b3:b4,b6:b4,b7:b4,b5:b1,b8:b1
cache sdom b1:-:b5:-:2:41,b4:b1:b3:b8:11:32,b3:b4:-:b6:14:17,b6:b4:-:b7:20:23,b7:b4:-:-:26:29,b5:b1:-:b4:5:8,b8:b1:-:-:35:38
cache loopnest 9 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
fstate scheduled,laidout
dcllen 17
end
pass 52 "late nilcheck"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b5:0 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 -1 0 - v43 b6:0,b3:0 b1:0
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b3 Plain p161:21:57:0:0 0 0 - - b7:0 b4:1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b3:0,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b5 Plain p161:21:31:0:0 0 0 - - b8:0 b1:1
b b8 Ret p2:507:2:1:0 0 0 - v51 - b5:0,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b3,b4,b5,b1
cache idom b1:-,b4:b1,b3:b4,b6:b4,b7:b4,b5:b1,b8:b1
cache sdom b1:-:b5:-:2:41,b4:b1:b3:b8:11:32,b3:b4:-:b6:14:17,b6:b4:-:b7:20:23,b7:b4:-:-:26:29,b5:b1:-:b4:5:8,b8:b1:-:-:35:38
cache loopnest 9 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
fstate scheduled,laidout
dcllen 17
end
pass 53 "flagalloc"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b5:0 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 -1 0 - v43 b6:0,b3:0 b1:0
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b3 Plain p161:21:57:0:0 0 0 - - b7:0 b4:1
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v15,v24,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b3:0,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v50,v46
b b5 Plain p161:21:31:0:0 0 0 - - b8:0 b1:1
b b8 Ret p2:507:2:1:0 0 0 - v51 - b5:0,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v50,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v30,v36,v27,v13,v21,v8,v7,v41,v38,v31,v19,v12,v11,v49,v53,v45,v44,v42,v40,v39,v37,v22,v35,v33,v32,v16,v14,v52,v9,v6,v5,v4,v3,v2
freeb b2
cache postorder b8,b7,b6,b3,b4,b5,b1
cache idom b1:-,b4:b1,b3:b4,b6:b4,b7:b4,b5:b1,b8:b1
cache sdom b1:-:b5:-:2:41,b4:b1:b3:b8:11:32,b3:b4:-:b6:14:17,b6:b4:-:b7:20:23,b7:b4:-:-:26:29,b5:b1:-:b4:5:8,b8:b1:-:-:35:38
cache loopnest 9 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
fstate scheduled,laidout
dcllen 17
end
pass 54 "regalloc"
aux a1 call "AuxCall{strings.HasSuffix}" a2 1 2 1 8 32 4 1
abiparam in 0 t2 a3 0,1 0
abiparam in 1 t2 a4 2,3 16
abiparam out 0 t3 a5 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b5:0 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 -1 0 - v43 b6:0,b3:0 b1:0
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b3 Plain p161:21:57:0:0 0 0 - - b7:0 b4:1
v v27 Copy t3 0 - p161:21:57:2:0 1 v50
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v30 Copy t17 0 - p161:21:57:2:0 1 v15
v v36 Copy t12 0 - p161:21:57:2:0 1 v24
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v30,v36,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b3:0,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v27,v46
b b5 Plain p161:21:31:0:0 0 0 - - b8:0 b1:1
v v13 Copy t3 0 - p2:507:30:2:0 1 v50
b b8 Ret p2:507:2:1:0 0 0 - v51 - b5:0,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v13,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v2,v3,v4,v5,v6,v7,v8,v9,v11,v12,v14,v16,v19,v21,v22,v31,v32,v33,v35,v37,v38,v39,v40,v41,v42,v44,v45,v49,v52,v53
freeb b2
cache postorder b8,b7,b6,b3,b4,b5,b1
cache idom b1:-,b4:b1,b3:b4,b6:b4,b7:b4,b5:b1,b8:b1
cache sdom b1:-:b5:-:2:41,b4:b1:b3:b8:11:32,b3:b4:-:b6:14:17,b6:b4:-:b7:20:23,b7:b4:-:-:26:29,b5:b1:-:b4:5:8,b8:b1:-:-:35:38
cache loopnest 9 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
fstate scheduled,laidout
regalloc 52 v13:R0,v15:R2,v17:R1,v18:R6,v20:R0,v24:R5,v25:R4,v26:R3,v27:R0,v28:R4,v29:R0,v30:R1,v34:R4,v36:R2,v46:R0,v47:R0,v48:R0,v50:ZERO,v51:[]
dcllen 17
end
pass 55 "loop rotate"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b5:0 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 -1 0 - v43 b6:0,b3:0 b1:0
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b3 Plain p161:21:57:0:0 0 0 - - b7:0 b4:1
v v27 Copy t3 0 - p161:21:57:2:0 1 v50
b b6 Plain p161:21:57:0:0 0 0 - - b7:1 b4:0
v v30 Copy t17 0 - p161:21:57:2:0 1 v15
v v36 Copy t12 0 - p161:21:57:2:0 1 v24
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v30,v36,v1
b b7 Plain p161:21:57:0:0 0 0 - - b8:1 b3:0,b6:0
v v47 Phi t3 0 - p161:21:57:0:0 1 v27,v46
b b5 Plain p161:21:31:0:0 0 0 - - b8:0 b1:1
v v13 Copy t3 0 - p2:507:30:2:0 1 v50
b b8 Ret p2:507:2:1:0 0 0 - v51 - b5:0,b7:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v13,v47
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v2,v3,v4,v5,v6,v7,v8,v9,v11,v12,v14,v16,v19,v21,v22,v31,v32,v33,v35,v37,v38,v39,v40,v41,v42,v44,v45,v49,v52,v53
freeb b2
cache postorder b8,b7,b6,b3,b4,b5,b1
cache idom b1:-,b4:b1,b3:b4,b6:b4,b7:b4,b5:b1,b8:b1
cache sdom b1:-:b5:-:2:41,b4:b1:b3:b8:11:32,b3:b4:-:b6:14:17,b6:b4:-:b7:20:23,b7:b4:-:-:26:29,b5:b1:-:b4:5:8,b8:b1:-:-:35:38
cache loopnest 9 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
fstate scheduled,laidout
regalloc 52 v13:R0,v15:R2,v17:R1,v18:R6,v20:R0,v24:R5,v25:R4,v26:R3,v27:R0,v28:R4,v29:R0,v30:R1,v34:R4,v36:R2,v46:R0,v47:R0,v48:R0,v50:ZERO,v51:[]
dcllen 17
end
pass 56 "trim"
f b1 t1 a1 53 8
b b1 ARM64LE p161:21:31:0:0 0 0 - v23 b4:0,b5:0 -
v v17 ArgIntReg t12 1 a10 p161:21:31:2:0 5 -
v v26 ArgIntReg t12 3 a12 p161:21:31:2:0 4 -
v v20 ArgIntReg t17 0 a9 p161:21:31:2:0 1 -
v v15 ArgIntReg t17 2 a11 p161:21:31:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v50 ARM64ZERO t3 0 - p0:0:0:0:0 2 -
v v10 InlMark t30 91 - p2:507:30:1:0 0 v1
v v23 ARM64CMP t29 0 - p161:21:16:1:0 1 v26,v17
b b4 ARM64EQ p161:21:57:0:0 -1 0 - v43 b6:0,b3:0 b1:0
v v34 ARM64ADD t12 0 - p161:21:35:0:0 2 v17,v26
v v24 ARM64SUB t12 0 - p161:21:35:0:0 2 v34,v17
v v25 ARM64SUB t12 0 - p161:21:35:0:0 1 v17,v34
v v18 ARM64SUB t12 0 - p161:21:42:0:0 1 v17,v26
v v28 ARM64ANDshiftRA t12 63 - p161:21:35:0:0 1 v18,v25
v v29 ARM64ADD t17 0 - p161:21:35:0:0 1 v20,v28
v v43 ARM64CMP t29 0 - p161:21:57:0:0 1 v26,v24
b b3 Plain p161:21:57:0:0 0 0 - - b8:1 b4:1
v v27 Copy t3 0 - p161:21:57:2:0 1 v50
b b6 Plain p161:21:57:0:0 0 0 - - b8:2 b4:0
v v30 Copy t17 0 - p161:21:57:2:0 1 v15
v v36 Copy t12 0 - p161:21:57:2:0 1 v24
v v46 ARM64LoweredMemEq t3 0 - p161:21:57:0:0 1 v29,v30,v36,v1
b b5 Plain p161:21:31:0:0 0 0 - - b8:0 b1:1
v v13 Copy t3 0 - p2:507:30:2:0 1 v50
b b8 Ret p2:507:2:1:0 0 0 - v51 - b5:0,b3:0,b6:0
v v48 Phi t3 0 - p2:507:30:1:0 1 v13,v27,v46
v v51 MakeResult t35 0 - p2:507:2:1:0 1 v48,v1
names s5,s6,s7,s8,s9,s10,s11,s12,s13
named s5 v48
named s6 v20
named s7 v17
named s8 v15
named s9 v26
named s10 v20
named s11 v17
named s12 v15
named s13 v26
splits s1/0/t17=s6,s1/8/t12=s7,s2/0/t17=s8,s2/8/t12=s9,s3/0/t17=s10,s3/8/t12=s11,s4/0/t17=s12,s4/8/t12=s13
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2,a6/t2/0/-/0=s3,a7/t2/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v2,v3,v4,v5,v6,v7,v8,v9,v11,v12,v14,v16,v19,v21,v22,v31,v32,v33,v35,v37,v38,v39,v40,v41,v42,v44,v45,v49,v52,v53
freeb b2
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5,a11:6,a12:7
cache linestarts 2:507:507,161:21:21
fstate scheduled,laidout
regalloc 52 v13:R0,v15:R2,v17:R1,v18:R6,v20:R0,v24:R5,v25:R4,v26:R3,v27:R0,v28:R4,v29:R0,v30:R1,v34:R4,v36:R2,v46:R0,v47:R0,v48:R0,v50:ZERO,v51:[]
dcllen 17
end
frontend
end
ptrcache t2,t5,t6,t7,t8,t10,t11,t12,t13,t14,t16,t17,t24,t27,t33
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t12,t15,t16,t25,t26,t13,t14,t3,t17,t18,t19,t20,t21,t22,t23,t34,t24,t33,t1,t2,t27,t28,t30,t29,t31,t32,t35
eof
"#

/-- `std/std/strings/HasSuffix,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "strings"
func "HasSuffix" 1
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
type t1 16 8 8 1 01 "string"
name n1 "s" PPARAM t1 1 "strings.s" 0 a3
name n2 "suffix" PPARAM t1 1 "strings.suffix" 0 a4
type t2 1 1 0 0 - "bool"
name n3 "~r0" PPARAMOUT t2 1 "strings.~r0" 0 a5
name n4 "s" PAUTO t1 1 "internal/stringslite.s" 0 a6
name n5 "suffix" PAUTO t1 1 "internal/stringslite.suffix" 0 a7
name n6 "~r0" PAUTO t2 1 "strings.~r0" 0 a8
name n7 ".autotmp_6" PAUTO t2 3 "strings..autotmp_6" 0 -
type t3 8 8 0 0 - "int"
name n8 ".autotmp_7" PAUTO t3 3 "strings..autotmp_7" 0 -
name n9 ".autotmp_8" PAUTO t3 3 "strings..autotmp_8" 0 -
name n10 ".autotmp_9" PAUTO t3 3 "strings..autotmp_9" 0 -
name n11 ".autotmp_10" PAUTO t3 3 "strings..autotmp_10" 0 -
name n12 ".autotmp_11" PAUTO t3 3 "strings..autotmp_11" 0 -
name n13 ".autotmp_12" PAUTO t1 3 "strings..autotmp_12" 0 -
type t4 8 8 8 1 01 "*uint8"
name n14 "s.ptr" PAUTO t4 3 "strings.s.ptr" 0 a13
name n15 "s.len" PAUTO t3 3 "strings.s.len" 0 a14
name n16 "suffix.ptr" PAUTO t4 3 "strings.suffix.ptr" 0 a15
name n17 "suffix.len" PAUTO t3 3 "strings.suffix.len" 0 a16
in n1 0 used
in n2 16 used
in n3 0 outregs
in n4 0 used
in n5 0 used
in n6 0 -
in n7 0 used,autotmp
in n8 0 used,autotmp
in n9 0 used,autotmp
in n10 0 used,autotmp
in n11 0 used,autotmp
in n12 0 used,autotmp
in n13 0 used,autotmp
in n14 0 used
in n15 0 used
in n16 0 used
in n17 0 used
out n1 0 used
out n2 16 used
opt n13 0 autotmp
opt n4 0 -
opt n14 0 -
opt n5 0 -
opt n16 0 -
opt n11 0 autotmp
opt n12 0 autotmp
opt n8 0 autotmp
opt n9 0 autotmp
opt n10 0 autotmp
opt n15 0 -
opt n17 0 -
opt n7 0 autotmp
opt n3 0 outregs
opt n6 0 -
stack 0 0 8
end
genin
posbase p2 "strings/strings.go" 1 1 -1 1 "strings/strings.go" "strings/strings.go" 1 1
sym y1 "strings.HasSuffix" 1
curfn p2:506:6:0:0 0 0
regargs 8192:0:t4,8193:8:t3,8194:16:t4,8195:24:t3
text y1 0 0 0 0 506 200080
end
prog0
sym y2 "strings.s" 0
sym y3 "strings.suffix" 0
sym y4 "gclocals\xc2\xb7itaneJMpbAudh9zNu5JnHA==" 0
sym y5 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y6 "strings.HasSuffix.arginfo1" 0
sym y7 "strings.HasSuffix.argliveinfo" 0
sym y8 "internal/stringslite.HasSuffix" 1
inl i91 - p2:507:30:0:0 y8 "HasSuffix"
posbase p161 "internal/stringslite/strings.go" 1 1 91 17 "internal/stringslite/strings.go" "internal/stringslite/strings.go" 1 1
sym y9 "runtime.memequal" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i32 0 0 p2:506:6:0:0
p 27 27 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/PARAM/0/0/y2/- 0 0 p2:506:6:2:0
p 28 28 0 0 0 - MOVD 0 REG/8194/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/PARAM/0/16/y3/- 0 0 p2:506:6:2:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:506:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:506:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p2:506:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p2:506:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:506:6:2:0
p 6 6 0 0 0 - NOP 0 _ 0 - _ 0 0 p0:0:0:0:0
p 7 7 0 0 0 - CMP 0 REG/8193/0/0/NONE/0/0/-/- 8195 - _ 0 0 p161:21:16:1:0
p 8 8 0 0 0 - BGT 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@24 0 0 p161:21:31:2:0
p 9 9 0 0 0 - ADD 0 REG/8195/0/0/NONE/0/0/-/- 8193 - REG/8196/0/0/NONE/0/0/-/- 0 0 p161:21:35:2:0
p 10 10 0 0 0 - SUB 0 REG/8193/0/0/NONE/0/0/-/- 8196 - REG/8197/0/0/NONE/0/0/-/- 0 0 p161:21:35:2:0
p 11 11 0 0 0 - SUB 0 REG/8196/0/0/NONE/0/0/-/- 8193 - REG/8196/0/0/NONE/0/0/-/- 0 0 p161:21:35:2:0
p 12 12 0 0 0 - SUB 0 REG/8195/0/0/NONE/0/0/-/- 8193 - REG/8198/0/0/NONE/0/0/-/- 0 0 p161:21:42:2:0
p 13 13 0 0 0 - AND 0 SHIFT/0/0/0/NONE/0/8715264/-/- 8198 - REG/8196/0/0/NONE/0/0/-/- 0 0 p161:21:35:2:0
p 14 14 0 0 0 - ADD 0 REG/8196/0/0/NONE/0/0/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p161:21:35:2:0
p 15 15 0 0 0 - CMP 0 REG/8197/0/0/NONE/0/0/-/- 8195 - _ 0 0 p161:21:57:2:0
p 16 16 0 0 0 - BEQ 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@19 0 0 p161:21:57:2:0
p 17 17 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p161:21:57:2:0
p 18 18 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@25 0 0 p161:21:57:2:0
p 19 19 0 0 0 - MOVD 0 REG/8194/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p161:21:57:2:0
p 20 20 0 0 0 - MOVD 0 REG/8197/0/0/NONE/0/0/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p161:21:57:2:0
p 21 21 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p161:21:57:2:0
p 22 22 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y9/- 0 0 p161:21:57:2:0
p 23 23 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@25 0 0 p161:21:57:2:0
p 24 24 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:507:30:1:0
p 25 25 0 0 0 - RET 0 _ 0 - _ 0 0 p2:507:2:1:0
p 26 26 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 506 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 8195 STP LDP
inlmark @24 91
funcaux y4 y5 - - y6 y7 -
needzero -
regargs -
text 0 0 - 0
symalign y4:4,y5:4,y6:1,y7:1
autot -
dbgentry 1
dbgslot 0 n6 t2 0
dbgslot 1 n1 t4 0
dbgslot 2 n1 t3 8
dbgslot 3 n2 t4 0
dbgslot 4 n2 t3 8
dbgslot 5 n14 t4 0
dbgslot 6 n15 t3 0
dbgslot 7 n16 t4 0
dbgslot 8 n17 t3 0
dbgvar 0 n1 1,2
dbgvar 1 n2 3,4
dbgvar 2 n4 5,6
dbgvar 3 n5 7,8
dbgloc 0 1:-10000:4:29:509308519308,4:29:6:30:9308519308,5:13:8:-10000:9308519308
dbgloc 1 1:-10000:6:36:529308539308,6:36:6:46:9308539308
dbgloc 2 1:-10000:4:29:509308519308,4:29:6:30:9308519308,5:13:8:-10000:9308519308
dbgloc 3 1:-10000:6:36:529308539308,6:36:6:46:9308539308
dbgregout n3
dbgpc 4:29:15,6:30:20,5:13:25,8:-10000:25,6:36:21,6:46:23
end
asm
sym y10 "runtime.morestack_noctxt" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i32 0 0 p2:506:6:0:0
p 29 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:506:6:0:0
p 30 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:506:6:0:0
p 31 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:506:6:0:0
p 32 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@41 0 0 p2:506:6:0:0
p 33 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:506:6:0:0
p 34 12 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p2:506:6:0:1
p 35 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:506:6:0:0
p 36 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:506:6:0:0
p 27 24 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/0/y2/- 0 0 p2:506:6:2:0
p 28 28 0 0 304 - MOVD 0 REG/8194/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/16/y3/- 0 0 p2:506:6:2:0
p 1 32 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:506:6:0:0
p 2 32 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p2:506:6:0:0
p 3 32 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y6/- 0 0 p2:506:6:0:0
p 4 32 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y7/- 0 0 p2:506:6:0:0
p 5 32 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:506:6:2:0
p 6 32 0 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p0:0:0:0:0
p 7 32 0 0 92 - CMP 0 REG/8193/0/0/NONE/2/0/-/- 8195 - NONE/0/0/0/NONE/1/0/-/- 0 0 p161:21:16:1:0
p 8 36 0 0 80 - BGT 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/24/-/@24 0 0 p161:21:31:2:0
p 9 40 0 0 23 - ADD 0 REG/8195/0/0/NONE/2/0/-/- 8193 - REG/8196/0/0/NONE/2/0/-/- 0 0 p161:21:35:2:0
p 10 44 0 0 23 - SUB 0 REG/8193/0/0/NONE/2/0/-/- 8196 - REG/8197/0/0/NONE/2/0/-/- 0 0 p161:21:35:2:0
p 11 48 0 0 23 - SUB 0 REG/8196/0/0/NONE/2/0/-/- 8193 - REG/8196/0/0/NONE/2/0/-/- 0 0 p161:21:35:2:0
p 12 52 0 0 23 - SUB 0 REG/8195/0/0/NONE/2/0/-/- 8193 - REG/8198/0/0/NONE/2/0/-/- 0 0 p161:21:42:2:0
p 13 56 0 0 51 - AND 0 SHIFT/0/0/0/NONE/8/8715264/-/- 8198 - REG/8196/0/0/NONE/2/0/-/- 0 0 p161:21:35:2:0
p 14 60 0 0 23 - ADD 0 REG/8196/0/0/NONE/2/0/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p161:21:35:2:0
p 15 64 0 0 92 - CMP 0 REG/8197/0/0/NONE/2/0/-/- 8195 - NONE/0/0/0/NONE/1/0/-/- 0 0 p161:21:57:2:0
p 16 68 0 0 80 - BEQ 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/19/-/@19 0 0 p161:21:57:2:0
p 17 72 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p161:21:57:2:0
p 18 76 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/25/-/@25 0 0 p161:21:57:2:0
p 19 80 0 0 301 - MOVD 0 REG/8194/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p161:21:57:2:0
p 20 84 0 0 301 - MOVD 0 REG/8197/0/0/NONE/2/0/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p161:21:57:2:0
p 21 88 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p161:21:57:2:0
p 22 88 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y9/- 0 0 p161:21:57:2:0
p 23 92 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/25/-/@25 0 0 p161:21:57:2:0
p 24 96 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:507:30:1:0
p 25 100 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:507:2:1:0
p 37 104 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:507:2:1:0
p 38 108 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:507:2:1:0
p 39 112 -16 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:507:2:1:0
p 40 112 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:506:6:0:0
p 41 112 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:506:6:0:0
p 42 112 0 0 436 - STP 0 REGREG/8192/0/0/NONE/7/8193/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p2:506:6:0:0
p 43 116 0 0 436 - STP 0 REGREG/8194/0/0/NONE/7/8195/-/- 0 - MEM/8383/0/0/NONE/87/24/-/- 0 0 p2:506:6:0:0
p 44 120 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:506:6:0:0
p 45 124 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y10/- 0 0 p2:506:6:0:0
p 46 128 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:506:6:0:0
p 47 128 0 0 245 - LDP 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REGREG/8192/0/0/NONE/7/8193/-/- 0 0 p2:506:6:0:0
p 48 132 0 0 245 - LDP 0 MEM/8383/0/0/NONE/87/24/-/- 0 - REGREG/8194/0/0/NONE/7/8195/-/- 0 0 p2:506:6:0:0
p 49 136 16 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@29 0 0 p2:506:6:0:0
fn y1 32 8 0 0 506 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 8195 STP LDP
inlmark @24 91
funcaux y4 y5 - - y6 y7 -
text 144 0 900b40f9ff6330eb49030054fe0f1ff8fd831ff8fd2300d1e00f00f9e21700f97f0001ebec0100542400038b850001cb240004cb260003cbc4fc848a0000048b7f0005eb60000054e0031faa06000014e10302aae20305aa0000009402000014e0031faafd835ff8fe0741f8c0035fd6e08700a9e28f01a9e3031eaa00000094e08740a9e28f41a9deffff1700000000 2
reloc 88 4 R_CALLARM64 0 y9
reloc 124 4 R_CALLARM64 0 y10
pcln y15 y16 y17 y18 y11,y12,y13,y14 y4,y5,_,_,_,y6,y7
usedfiles 1,17
inltree 0 -1 p2:507:30:0:0 y8 "HasSuffix" 96
data y4 Sxxx 0 4 8000 02000000030000000500 0
data y5 Sxxx 0 4 8000 0200000000000000 0
data y6 SDATA 13 1 8000 fe00080808fdfe10081808fdff 0
data y7 SDATA 2 1 8000 0000 0
data y11 SRODATA 11 1 28000 0001010202190104020400 0
data y12 SRODATA 7 1 28000 00160406030800 0
data y13 SRODATA 0 1 28000 - 0
data y14 SRODATA 5 1 28000 0008041c00 0
data y15 SRODATA 7 1 28000 020420171f0900 0
data y16 SRODATA 7 1 28000 040820101f0c00 0
data y17 SRODATA 12 1 28000 f60708c90710cc0704010800 0
data y18 SRODATA 7 1 28000 00080210010c00 0
end
dwarf
sym y19 "" 0
sym y20 "" 0
sym y21 "" 0
sym y22 "" 0
posbase p19 "internal/stringslite/strings.go" 1 1 -1 17 "internal/stringslite/strings.go" "internal/stringslite/strings.go" 1 1
sym y23 "go:info.internal/stringslite.HasSuffix$abstract" 0
sym y24 "go:info.string" 0
sym y25 "go:info.bool" 0
sym y26 "type:bool" 0
dwfn y19 y20 y21 - y22 "strings.HasSuffix" 1:506 1 0 1 138
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2,n3
dwinlfn y8 y23
dwinldcl y8 "s" 0 p19:20:16:0:0
dwinldcl y8 "suffix" 0 p19:20:19:0:0
dwinldcl y8 "~r0" 0 p19:20:34:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "string" 0 0 1 p2:506:16:0:0
dwname n2 1 1 0 0 0 0 16 0 - - "string" 0 0 1 p2:506:19:0:0
dwname n13 1 0 1 0 0 0 0 0 - - "string" 0 0 1 p161:21:35:0:0
dwname n4 1 0 0 1 0 0 0 0 - - "string" 0 0 1 p161:20:16:0:0
dwname n14 1 0 0 0 0 0 0 0 - - "*uint8" 0 0 1 p161:20:16:0:0
dwname n5 1 0 0 1 0 0 0 0 - - "string" 0 0 1 p161:20:19:0:0
dwname n16 1 0 0 0 0 0 0 0 - - "*uint8" 0 0 1 p161:20:19:0:0
dwname n11 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p161:21:46:0:0
dwname n12 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p161:21:35:0:0
dwname n8 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p161:21:12:0:0
dwname n9 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p161:21:22:0:0
dwname n10 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p161:21:39:0:0
dwname n15 1 0 0 0 0 0 0 0 - - "int" 0 0 1 p161:20:16:0:0
dwname n17 1 0 0 0 0 0 0 0 - - "int" 0 0 1 p161:20:19:0:0
dwname n7 1 0 1 0 0 0 0 0 - - "bool" 0 0 1 p161:21:31:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "bool" 0 0 1 p2:506:34:0:0
dwname n6 1 0 0 1 0 0 0 0 - - "bool" 0 0 1 p161:20:34:0:0
var 0 0 "s" 5 1 0 0 0 8 y24 "strings/strings.go" 506 16 0 0 0 0 v0
var 1 0 "suffix" 5 1 0 0 0 24 y24 "strings/strings.go" 506 19 0 1 0 0 v1
var 2 0 "~r0" 5 1 1 0 0 0 y25 "strings/strings.go" 506 34 0 2 0 0 -
var 3 0 "s" 5 1 0 1 0 -8 y24 "internal/stringslite/strings.go" 20 16 92 0 1 0 v2
var 4 0 "suffix" 5 1 0 1 0 -8 y24 "internal/stringslite/strings.go" 20 19 92 1 1 0 v3
scope 0 0 - 0,1,2,3,4
inlcall 0 91 1:507 y23 - 1 32:96 3,4
dieref y19 9 y23 0
dieref y19 11 y23 1
data y19 SDWARFFCN 113 0 0 03737472696e67732e4861735375666669780000009001019c02000000fa03012d730000fa0300000000000000002d7375666669780000fa0300000000000000002e7e72300001fa03000000000009000000000000000002000000fb032900000000000000002900000000000000000000 13
reloc 0 0 R_USETYPE 0 y26
reloc 19 2 R_DWTXTADDR_U2 0 y1
reloc 38 4 R_DWARFSECREF 0 y24
reloc 42 4 R_DWARFSECREF 0 y20
reloc 57 4 R_DWARFSECREF 0 y24
reloc 61 4 R_DWARFSECREF 32 y20
reloc 73 4 R_DWARFSECREF 0 y25
reloc 79 4 R_DWARFSECREF 0 y23
reloc 83 4 R_DWARFSECREF 0 y21
reloc 94 4 R_DWARFSECREF 0 y23
reloc 98 4 R_DWARFSECREF 55 y20
reloc 103 4 R_DWARFSECREF 0 y23
reloc 107 4 R_DWARFSECREF 87 y20
data y20 SDWARFLOC 110 0 0 01000004004006509308519308044054059308519308046464059308519308000100000400580652930853930804585c0593085393080001000004004006509308519308044054059308519308046464059308519308000100000400580652930853930804585c05930853930800 4
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 33 2 R_DWTXTADDR_U2 0 y1
reloc 56 2 R_DWTXTADDR_U2 0 y1
reloc 88 2 R_DWTXTADDR_U2 0 y1
data y21 SDWARFRANGE 7 0 0 01000004206000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y22 SDWARFLINES 45 0 0 0009020000000000000000040203f403140a870687041206039f7c5b0637040206022503e103faae0220000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `HasSuffix`, with the home `R0` of the removed `v47`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G38 checks: `lc0` without the homes of removed values. -/
def lc : LocCtx := liveCtx lc0

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

/-- The PC table `checkG39` gives. -/
def tab : PcTab :=
  [(1, [7, 7, 7, 7, 7, 7, 7, 7, 10]), (4, [11, 12, 13, 14, 15, 16, 17, 18]), (3, [19, 20]),
    (6, [21, 22, 23, 25]), (5, [26, 27]), (8, [27, 27, 27])]

/-- The class table `checkG39` gives. -/
def kt : KTab := (match checkG39 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 4).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG39`. -/
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

/-- The `runLoc` state at the entry of `b4`: `len(s) = 5` (`v17`) in `R1`, `len(suffix) = 2`
(`v26`) in `R3`, every other register `poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 1 then .int .w64 5 else if i.val = 3 then .int .w64 2 else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine at the entry of `b4`: `X1 = 5`, `X3 = 2`, the activation's `g` and `FP`, the PC
of `v34`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 1 then 5 else if k = 3 then 2 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 4 0, mem := fun _ => 0 }

/-- The register holds the 64-bit integer 7. -/
def is7 : Option Val → Bool
  | some (.int .w64 x) => x == 7
  | _ => false

theorem is7_spec {o : Option Val} (h : is7 o = true) : o = some (.int .w64 7) := by
  unfold is7 at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on `HasSuffix`: it holds an arm64 op; `checkG39` accepts it
with `tab` and `kt` and `checkG38` does not; every value refers to values of the function
(`refsLive`); the removed `v47` has the home `R0` in `lc0` and none in `lc`; it accesses no frame
variable and has no home slot; `b4` holds `v34` (`ADD v17 v26`) at index 0, where `R1` and `R3`
have class 64 and G35's table is empty; `stepLoc` runs `v34` from `s0` to `R4 = 7`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG39 lc0 ps bs g).toOption == some (tab, kt) && (checkG38 lc0 ps bs g).toOption.isNone &&
    refsLive lc0 && lc0.home 47 == some (.reg 0) && lc.home 47 == none &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 4 && (lc.ctx.f.block? 4).isSome &&
    (lc.ctx.f.value? 34).isSome && blk.values[0]? == some 34 &&
    (val 34).op == .ARM64ADD && (kAt lc kt 4 blk 0).get 1 == some 64 &&
    (kAt lc kt 4 blk 0).get 3 == some 64 && uL35 lc (uIn35 lc 4) blk 0 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 34)) fun s1 => is7 s1.regs[4]?

theorem g39_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG39 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG38 lc0 ps bs g).toOption = none ∧ refsLive lc0 = true ∧
      lc0.home 47 = some (.reg 0) ∧ lc.home 47 = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      4 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 4 = some blk ∧
      lc.ctx.f.value? 34 = some (val 34) ∧ blk.values[0]? = some 34 ∧
      (val 34).op = .ARM64ADD ∧ (kAt lc kt 4 blk 0).get 1 = some 64 ∧
      (kAt lc kt 4 blk 0).get 3 = some 64 ∧ uL35 lc (uIn35 lc 4) blk 0 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 34)) (fun s1 => is7 s1.regs[4]?) = true := by
  have hf := g39_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h38, hr, h47, h47', hav, hsl, hm1, hbs, hvs, hi0, hop, hk1, hk3, hu0, hrun⟩ :=
    hf
  refine ⟨hl, ?_, h38, hr, h47, h47', hav, hsl, hm1, ?_, ?_, hi0, hop, hk1, hk3, hu0, hrun⟩
  · revert hres; cases checkG39 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g39Env (hc : checkG39 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
              checkG38_spec hl (checkG39_spec hc).2
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
              checkG38_spec hl (checkG39_spec hc).2
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

/-! ## `v34`: `ADD R3, R1, R4` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 1 ∧ x = .int .w64 5) ∨ (r = 3 ∧ x = .int .w64 2) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · split at h
      · rename_i h3; exact Or.inr (Or.inl ⟨h3, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatch0 : LocMatch E s0 4 0 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl (show m0.x 1 = 5 by decide)
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl (show m0.x 3 = 2 by decide)
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g39Inv0 (h1 : (kAt lc kt 4 blk 0).get 1 = some 64)
    (h3 : (kAt lc kt 4 blk 0).get 3 = some 64) :
    G3Inv E lc (kAt lc kt 4 blk 0) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h1] at hc; cases hc; rfl
    · rw [h3] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v34`, `ADD`: none apply. -/
theorem pre34 {s : LocState} (hop : (val 34).op = .ARM64ADD) : G38Pre lc s (val 34) := by
  have hne : ∀ o : Op, o ≠ .ARM64ADD → (val 34).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl
  · intro _ _ hl; rw [hop] at hl; cases hl

/-- **G39 on `strings.HasSuffix`**: `lc0` keeps the home `R0` of `v47`, a `Phi` `trim` removed, so
`checkG38` rejects the function (`v47: register value of shape Ty.other`); `checkG39` accepts it,
and `lc = liveCtx lc0` drops that home. From the state at the entry of `b4` with `len(s) = 5` in
`R1` and `len(suffix) = 2` in `R3`, `v34 = ADD v17 v26` runs alike under `lc0` and `lc`
(`stepLoc_live`) to `R4 = 7`, and `g39_value` runs `ADD R3, R1, R4`: the machine state, related to
it before `v24` under an activation extending `E` that is again a `G28Env`, has `X4 = 7`. -/
theorem genG39_witness :
    lc0.home 47 = some (.reg 0) ∧ (liveCtx lc0).home 47 = none ∧
      (checkG38 lc0 ps bs g).toOption = none ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc0 s0 (val 34) = .ok s1 ∧
        stepLoc GenG2.env (liveCtx lc0) s0 (val 34) = .ok s1 ∧
        s1.regs[4]? = some (.int .w64 7) ∧
        E.Extends E1 ∧ G28Env (liveCtx lc0) g L ps 0 tab E1 ∧
        PStar GenG2.H0 L ps.toList 0 m0 m1 ∧ LocMatch E1 s1 4 1 m1 ∧ m1.x 4 = 7 := by
  obtain ⟨hl, hc, h38, hr, h47, h47', hav, hsl, hm1, hb, hv34, hi0, hop, hk1, hk3, hu0, hrun⟩ :=
    facts
  obtain ⟨s1, hs1, hr4⟩ := GenG1.okThen_spec hrun
  have hr4 := is7_spec hr4
  have hE := g39Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64ADD → (val 34).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g39_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hm0 : 4 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 4 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 34 = some (val 34) := by
    rw [← liveCtx_ctx (lc := lc0)]; exact hv34
  obtain ⟨hid, hargs⟩ := refsLive_spec hr hv0
  have hs0 : stepLoc GenG2.env lc0 s0 (val 34) = .ok s1 := by
    rw [← stepLoc_live s0 hid hargs]; exact hs1
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g39_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi0 hv0 (by rw [hop]; rfl) locMatch0 (g39Inv0 hk1 hk3)
    (by change UOKL m0 (uL35 lc (uIn35 lc 4) blk 0); rw [hu0]; intro e he; cases he) (pre34 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  have hx4 : m1.x 4 = 7 := valRel_i64 hA ((hm1'.regs 4 _ hr4).1 4 rfl)
  exact ⟨h47, h47', h38, s1, E1, m1, hs0, hs1, hr4, hx1, hE1, hp1, hm1', hx4⟩

end GoFV.Proof.Witness.GenG39
