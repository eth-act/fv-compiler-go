import GoFV.Proof.Gen.G25
import GoFV.Proof.Witness.GenG24

/-!
# Non-vacuity witness: slice G25 of the genssa validator on `reflect.flag.ro`

`std/std/encoding/binary/struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer;
reflect.flag }.reflect.ro,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`): the method the
compiler generates for the struct that embeds `reflect.flag`, with `flag.ro` (`reflect/value.go`)
inlined:

```go
func (f flag) ro() flag {
	if f&flagRO != 0 {
		return flagStickyRO
	}
	return 0
}
```

`checkG24` rejects it (`v14 = CSEL0 [NotEqual] v12 v18`); `checkG25` accepts it with the PC
table `tab` and the class table `kt`. Block `b1`: `v11 = ANDconst [96] v17` (`AND $96, R2, R1`),
`v18 = CMPconst [0] v11` (`CMP $0, R1`), `v12 = MOVDconst [32]` (`MOVD $32, R1`) and `v14`
(`CSEL NE, R1, ZR, R0`), then the `RET`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g25_facts`),
`stepLoc` runs `v14` from a state with `flagStickyRO = 32` in `R1` and the flags of `CMP $0, R1`
on `f & flagRO = 32` (`NE`): `R0` then holds 32. On a framed activation with `G10Env` (as
`GenG23`'s) with `X1 = 32` and `NZCV` those flags, `g25_value` runs the `CSEL`: the machine's `X0`
is 32 (`genG25_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG25

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/encoding/binary/struct { … reflect.flag }.reflect.ro,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "encoding/binary"
func "struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }.reflect.ro" 1 0 0
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
config localpkg "encoding/binary"
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
type t5 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t6 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t7 UINT8 1 1 0 comparable,named "abi.TFlag" "internal/abi.TFlag"
type t8 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t9 UINT8 1 1 0 comparable,named "abi.Kind" "internal/abi.Kind"
type t11 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t12 BOOL 1 1 0 comparable,named "bool" "bool"
type t10 FUNC 8 8 8 hasptr,direct "func(unsafe.Pointer, unsafe.Pointer) bool" "func(unsafe.Pointer, unsafe.Pointer) bool" 0 2 1
field 0 "" t11 ? 0
field 1 "" t11 ? 0
field 2 "" t12 ? 0
type t14 UINT8 1 1 0 comparable,named "byte" "uint8"
type t13 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t14
type t15 INT32 4 4 0 comparable,named "abi.NameOff" "internal/abi.NameOff"
type t16 INT32 4 4 0 comparable,named "abi.TypeOff" "internal/abi.TypeOff"
type t4 STRUCT 48 8 40 hasptr,named "abi.Type" "internal/abi.Type" 11
field 0 "Size_" t5 0 0
field 1 "PtrBytes" t5 8 0
field 2 "Hash" t6 16 0
field 3 "TFlag" t7 20 0
field 4 "Align_" t8 21 0
field 5 "FieldAlign_" t8 22 0
field 6 "Kind_" t9 23 0
field 7 "Equal" t10 24 0
field 8 "GCData" t13 32 0
field 9 "Str" t15 40 0
field 10 "PtrToThis" t16 44 0
type t3 PTR 8 8 8 hasptr,direct,comparable "*abi.Type" "*internal/abi.Type" t4
type t17 UINTPTR 8 8 0 comparable,named "reflect.flag" "reflect.flag"
type t2 STRUCT 24 8 16 hasptr,shape,comparable,named "go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }" "go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }" 3
field 0 "typ_" t3 0 0
field 1 "ptr" t11 8 0
field 2 "flag" t17 16 1
type t1 FUNC 8 8 8 hasptr,direct "method(go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }) func() reflect.flag" "method(go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }) func() reflect.flag" 1 0 1
field 0 "f" t2 ? 0
field 1 "" t17 ? 0
aux a2 sym "go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }.reflect.ro" "go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }.reflect.ro" 1 - 0 - - - - 0
posbase p13 "reflect/value.go" 1 1 -1
aux a3 name "reflect.f" "f" PPARAM t2 0 1 used p13:90:7:0:0
aux a4 name "go.shape.~r0" "~r0" PPARAMOUT t17 0 1 - p13:90:20:0:0
aux a1 call "AuxCall{go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }.reflect.ro}" a2 1 1 1 8 24 3 1
abiparam in 0 t2 a3 0,1,2 0
abiparam out 0 t17 a4 0 -1
type t18 INT8 1 1 0 comparable,named "int8" "int8"
type t19 INT16 2 2 0 comparable,named "int16" "int16"
type t20 INT32 4 4 0 comparable,named "int32" "int32"
type t21 INT64 8 8 0 comparable,named "int64" "int64"
type t22 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t23 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t24 INT 8 8 0 comparable,named "int" "int"
type t25 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t26 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t27 UINT 8 8 0 comparable,named "uint" "uint"
type t28 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t29 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t30 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t20
type t31 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t6
type t32 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t24
type t33 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t5
type t34 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t25
type t35 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t26
type t36 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t29
type t37 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t38 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t39 SSA ? ? ? - "mem" ""
type t40 SSA ? ? ? - "flags" ""
type t41 SSA ? ? ? - "void" ""
type t42 SSA 16 8 ? - "int128" ""
type t43 RESULTS ? ? ? - "mem" "" 1 t39
posbase p610 "reflect/value.go" 1 1 470
type t44 PTR 8 8 8 hasptr,direct,comparable "*go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }" "*go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }" t2
type t45 PTR 8 8 8 hasptr,direct,comparable "*reflect.flag" "*reflect.flag" t17
posbase p1 "<autogenerated>" 1 1 -1
type t46 RESULTS ? ? ? - "reflect.flag,mem" "" 2 t17,t39
slot s1 a3 t2 0 - 0
aux a5 name "reflect.f" "f" PAUTO t17 0 1 used p610:90:7:0:0
slot s2 a5 t17 0 - 0
aux a6 name "go.shape.~r0" "~r0" PAUTO t17 0 1 - p610:90:20:0:0
slot s3 a6 t17 0 - 0
f b1 t1 a1 16 4
typs Bool=t12,Int8=t18,Int16=t19,Int32=t20,Int64=t21,UInt8=t8,UInt16=t22,UInt32=t6,UInt64=t23,Int=t24,Float32=t25,Float64=t26,UInt=t27,Uintptr=t5,String=t28,BytePtr=t29,Int32Ptr=t30,UInt32Ptr=t31,IntPtr=t32,UintptrPtr=t33,Float32Ptr=t34,Float64Ptr=t35,BytePtrPtr=t36,Complex64=t37,Complex128=t38,UnsafePtr=t11,Mem=t39,Flags=t40,Void=t41,Int128=t42,ResultMem=t43
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 4 -
v v2 SP t5 0 - p0:0:0:0:0 2 -
v v3 SB t5 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t44 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t45 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:0:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v15 Copy t39 0 - p1:1:0:2:0 1 v1
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v15
names s1,s2,s3
named s1 v6
named s2 v8
named s3 v7,v13,v7,v14
splits -
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev -
freeb -
dcllen 4
end
pass 1 "number lines"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 4 -
v v2 SP t5 0 - p0:0:0:0:0 2 -
v v3 SB t5 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t44 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t45 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v15 Copy t39 0 - p1:1:0:2:0 1 v1
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v15
names s1,s2,s3
named s1 v6
named s2 v8
named s3 v7,v13,v7,v14
splits -
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev -
freeb -
cache postorder b4,b3,b2,b1
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 5 -
v v2 SP t5 0 - p0:0:0:0:0 2 -
v v3 SB t5 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t44 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t45 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v15 Copy t39 0 - p1:1:0:2:0 0 v1
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s1,s2,s3
named s1 v6
named s2 v8
named s3 v7,v13,v7,v14
splits -
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev -
freeb -
cache postorder b4,b3,b2,b1
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 3 "early deadcode"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s1,s2,s3
named s1 v6
named s2 v8
named s3 v7,v13,v14
splits -
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 4 "short circuit"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s1,s2,s3
named s1 v6
named s2 v8
named s3 v7,v13,v14
splits -
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 5 "decompose user"
slot s4 a3 t3 0 - 0
slot s5 a3 t11 8 - 0
slot s6 a3 t17 16 - 0
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3,s4,s5,s6
named s2 v8
named s3 v7,v13,v14
named s4 -
named s5 -
named s6 -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 7 "opt"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 8 "zero arg cse"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 9 "opt deadcode"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 10 "generic cse"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 11 "phiopt"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 12 "gcse deadcode"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 13 "nilcheckelim"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 14 "prove"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 15 "divisible"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 16 "divmod"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 17 "middle opt"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 18 "known bits"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 19 "early fuse"
f b1 t1 a1 16 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 1 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v15,v5,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 20 "expand calls"
aux a7 nameoff "f+0" a3 0
aux a8 nameoff "f+8" a3 8
aux a9 nameoff "f+16" a3 16
f b1 t1 a1 18 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 3 -
v v6 StructMake t2 0 - p610:91:17:2:0 1 v3,v2,v17
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v8 StructSelect t17 2 - p1:1:0:0:0 1 v6
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v8,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v15 SB t5 0 - p0:0:0:0:0 0 -
v v5 SP t5 0 - p0:0:0:0:0 2 -
v v4 OffPtr t44 0 - p0:0:0:0:0 0 v5
v v3 ArgIntReg t3 0 a7 p610:91:17:2:0 1 -
v v2 ArgIntReg t11 1 a8 p610:91:17:2:0 1 -
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 LocalAddr t45 0 a4 p1:1:0:0:0 0 v5,v1
names s2,s3
named s2 v8
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,v4,32=v13,96=v10
freev -
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 21 "decompose builtin"
f b1 t1 a1 18 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 3 -
v v6 StructMake t2 0 - p610:91:17:2:0 0 v3,v2,v17
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v17,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v15 SB t5 0 - p0:0:0:0:0 0 -
v v5 SP t5 0 - p0:0:0:0:0 2 -
v v4 OffPtr t44 0 - p0:0:0:0:0 0 v5
v v3 ArgIntReg t3 0 a7 p610:91:17:2:0 1 -
v v2 ArgIntReg t11 1 a8 p610:91:17:2:0 1 -
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 2 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 LocalAddr t45 0 a4 p1:1:0:0:0 0 v5,v1
names s2,s3
named s2 -
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,v4,32=v13,96=v10
freev v8
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 22 "softfloat"
f b1 t1 a1 18 4
b b1 If p610:91:17:0:0 0 0 - v12 b3:0,b2:0 -
v v1 InitMem t39 0 - p0:0:0:0:0 3 -
v v6 StructMake t2 0 - p610:91:17:2:0 0 v3,v2,v17
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v17,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v15 SB t5 0 - p0:0:0:0:0 0 -
v v5 SP t5 0 - p0:0:0:0:0 2 -
v v4 OffPtr t44 0 - p0:0:0:0:0 0 v5
v v3 ArgIntReg t3 0 a7 p610:91:17:2:0 1 -
v v2 ArgIntReg t11 1 a8 p610:91:17:2:0 1 -
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 2 -
b b2 Plain p1:1:0:1:0 0 0 - - b4:1 b1:1
b b3 Plain p1:1:0:1:0 0 0 - - b4:0 b1:0
b b4 Ret p1:1:0:1:0 0 0 - v16 - b3:0,b2:0
v v14 Phi t17 0 - p1:1:0:0:0 1 v13,v7
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 LocalAddr t45 0 a4 p1:1:0:0:0 0 v5,v1
names s2,s3
named s2 -
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,v4,32=v13,96=v10
freev v8
freeb -
cache postorder b4,b3,b2,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b2:-:2:23,b2:b1:-:b3:5:8,b3:b1:-:b4:11:14,b4:b1:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 23 "branchelim"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 3 -
v v6 StructMake t2 0 - p610:91:17:2:0 0 v3,v2,v17
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v17,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v15 SB t5 0 - p0:0:0:0:0 0 -
v v5 SP t5 0 - p0:0:0:0:0 2 -
v v4 OffPtr t44 0 - p0:0:0:0:0 0 v5
v v3 ArgIntReg t3 0 a7 p610:91:17:2:0 1 -
v v2 ArgIntReg t11 1 a8 p610:91:17:2:0 1 -
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 2 -
v v14 CondSelect t17 0 - p1:1:0:0:0 1 v13,v7,v12
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 LocalAddr t45 0 a4 p1:1:0:0:0 0 v5,v1
b b2 BlockInvalid p1:1:0:1:0 0 0 - - - -
b b3 BlockInvalid p1:1:0:1:0 0 0 - - - -
b b4 BlockInvalid p1:1:0:1:0 0 0 - - - -
names s2,s3
named s2 -
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,v4,32=v13,96=v10
freev v8
freeb -
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 24 "late opt"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v17,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 CondSelect t17 0 - p1:1:0:0:0 1 v13,v7,v12
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
b b2 BlockInvalid p1:1:0:1:0 0 0 - - - -
b b3 BlockInvalid p1:1:0:1:0 0 0 - - - -
b b4 BlockInvalid p1:1:0:1:0 0 0 - - - -
names s2,s3
named s2 -
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v18,v2,v3,v4,v5,v15,v6,v8
freeb -
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 25 "dead auto elim"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v17,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 CondSelect t17 0 - p1:1:0:0:0 1 v13,v7,v12
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
b b2 BlockInvalid p1:1:0:1:0 0 0 - - - -
b b3 BlockInvalid p1:1:0:1:0 0 0 - - - -
b b4 BlockInvalid p1:1:0:1:0 0 0 - - - -
names s2,s3
named s2 -
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v18,v2,v3,v4,v5,v15,v6,v8
freeb -
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 26 "sccp"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v17,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 CondSelect t17 0 - p1:1:0:0:0 1 v13,v7,v12
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
b b2 BlockInvalid p1:1:0:1:0 0 0 - - - -
b b3 BlockInvalid p1:1:0:1:0 0 0 - - - -
b b4 BlockInvalid p1:1:0:1:0 0 0 - - - -
names s2,s3
named s2 -
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v18,v2,v3,v4,v5,v15,v6,v8
freeb -
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 27 "generic deadcode"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v17,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 CondSelect t17 0 - p1:1:0:0:0 1 v13,v7,v12
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s3
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v18,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 28 "late fuse"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v17,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 CondSelect t17 0 - p1:1:0:0:0 1 v13,v7,v12
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s3
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v18,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 29 "check bce"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v17,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 CondSelect t17 0 - p1:1:0:0:0 1 v13,v7,v12
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s3
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v18,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 30 "dse"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v17,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 CondSelect t17 0 - p1:1:0:0:0 1 v13,v7,v12
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s3
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v18,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 31 "memcombine"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v17,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 CondSelect t17 0 - p1:1:0:0:0 1 v13,v7,v12
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s3
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v18,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 32 "writebarrier"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v7 Const64 t17 0 - p0:0:0:0:0 2 -
v v10 Const64 t17 96 - p0:0:0:0:0 1 -
v v13 Const64 t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 And64 t17 0 - p610:91:6:1:0 1 v17,v10
v v12 Neq64 t12 0 - p610:91:14:0:0 1 v11,v7
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 CondSelect t17 0 - p1:1:0:0:0 1 v13,v7,v12
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s3
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts 0=v7,32=v13,96=v10
freev v18,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 33 "lower"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 34 "addressing modes"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 35 "late lower"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 36 "pair"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v7,v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache auxmap a3:1,-:2
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 38 "lowered cse"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 39 "elim unread autos"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 41 "lowered deadcode"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 42 "checkLower"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 43 "loop invariant"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 45 "tighten"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 46 "late deadcode"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 47 "critical"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 48 "phi tighten"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 49 "likelyadjust"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
dcllen 4
end
pass 50 "layout"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
fstate laidout
dcllen 4
end
pass 51 "schedule"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
fstate scheduled,laidout
dcllen 4
end
pass 52 "late nilcheck"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
fstate scheduled,laidout
dcllen 4
end
pass 53 "flagalloc"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v13 ARM64MOVDconst t17 32 - p0:0:0:0:0 1 -
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v13,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v12,v10,v7,v2,v3,v4,v5,v15,v6,v8
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
fstate scheduled,laidout
dcllen 4
end
pass 54 "regalloc"
aux a1 call "AuxCall{go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }.reflect.ro}" a2 1 1 1 8 24 3 1
abiparam in 0 t2 a3 0,1,2 0
abiparam out 0 t17 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
v v12 ARM64MOVDconst t17 32 - p1:1:0:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v12,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v2,v3,v4,v5,v6,v7,v8,v10,v15
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
fstate scheduled,laidout
regalloc 18 v11:R1,v12:R1,v14:R0,v16:[],v17:R2
dcllen 4
end
pass 55 "loop rotate"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
v v12 ARM64MOVDconst t17 32 - p1:1:0:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v12,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v2,v3,v4,v5,v6,v7,v8,v10,v15
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
fstate scheduled,laidout
regalloc 18 v11:R1,v12:R1,v14:R0,v16:[],v17:R2
dcllen 4
end
pass 56 "trim"
f b1 t1 a1 18 4
b b1 Ret p610:91:17:0:0 0 0 - v16 - -
v v17 ArgIntReg t17 2 a9 p610:91:17:2:0 1 -
v v1 InitMem t39 0 - p0:0:0:0:0 2 -
v v11 ARM64ANDconst t17 96 - p610:91:6:1:0 1 v17
v v9 InlMark t41 470 - p1:1:0:1:0 0 v1
v v18 ARM64CMPconst t40 0 - p610:91:14:0:0 1 v11
v v12 ARM64MOVDconst t17 32 - p1:1:0:2:0 1 -
v v14 ARM64CSEL0 t17 4577 - p1:1:0:0:0 1 v12,v18
v v16 MakeResult t46 0 - p1:1:0:0:0 1 v14,v1
names s3
named s3 v13,v14
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s4,s1/8/t11=s5,s1/16/t17=s6
canon a3/t2/0/-/0=s1,a5/t17/0/-/0=s2,a6/t17/0/-/0=s3
consts -
freev v2,v3,v4,v5,v6,v7,v8,v10,v15
freeb b4,b3,b2
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a9:3
cache linestarts 1:1:1,610:91:91
fstate scheduled,laidout
regalloc 18 v11:R1,v12:R1,v14:R0,v16:[],v17:R2
dcllen 4
end
frontend
end
ptrcache t4,t5,t6,t8,t11,t12,t13,t14,t18,t19,t20,t21,t22,t23,t24,t25,t26,t28,t29,t36
typelink t8=t14,t13=t29,t39=t43
typecmp t9 t14 gt
typeorder t18,t9,t8=t14,t7,t19,t22,t20,t15,t16,t6,t21,t23,t24,t27,t17,t5,t37,t38,t25,t26,t12,t13=t29,t30,t31,t32,t45,t33,t34,t35,t36,t3,t44,t10,t1,t4,t2,t28,t11,t39,t41,t40,t42,t43,t46
eof
"#

/-- `std/std/encoding/binary/struct { … reflect.flag }.reflect.ro,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "encoding/binary"
func "struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }.reflect.ro" 1
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
type t1 24 8 16 1 03 "go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }"
name n1 "f" PPARAM t1 1 "reflect.f" 0 a3
type t2 8 8 0 0 - "reflect.flag"
name n2 "~r0" PPARAMOUT t2 1 "go.shape.~r0" 0 a4
name n3 "f" PAUTO t2 1 "reflect.f" 0 a5
name n4 "~r0" PAUTO t2 1 "go.shape.~r0" 0 a6
in n1 0 used
in n2 0 outregs
in n3 0 used
in n4 0 -
out n1 0 used
opt n3 0 -
opt n2 0 outregs
opt n4 0 -
stack 0 0 8
end
genin
posbase p1 "<autogenerated>" 1 1 -1 0 "<autogenerated>" "<autogenerated>" 1 1
type t3 8 8 8 1 01 "*abi.Type"
type t4 8 8 8 1 01 "unsafe.Pointer"
sym y1 "go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }.reflect.ro" 1
curfn p1:1:0:0:0 0 0
regargs 8192:0:t3,8193:8:t4,8194:16:t2
text y1 0 0 23 0 1 200091
end
prog0
sym y2 "reflect.f" 0
sym y3 "gclocals\xc2\xb7TswRR9Pia9Wsluv5u1sUnA==" 0
sym y4 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y5 "go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }.reflect.ro.arginfo1" 0
sym y6 "go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }.reflect.ro.argliveinfo" 0
sym y7 "reflect.flag.ro" 1
inl i470 - p1:1:0:0:0 y7 "flag.ro"
posbase p610 "reflect/value.go" 1 1 470 11 "reflect/value.go" "reflect/value.go" 1 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i24 0 0 p1:1:0:0:0
p 14 14 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/PARAM/0/0/y2/- 0 0 p1:1:0:2:0
p 15 15 0 0 0 - MOVD 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/PARAM/0/8/y2/- 0 0 p1:1:0:2:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p1:1:0:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p1:1:0:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p1:1:0:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p1:1:0:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p1:1:0:2:0
p 12 12 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p1:1:0:1:0
p 6 6 0 0 0 - AND 0 CONST/0/0/0/NONE/0/96/-/- 8194 - REG/8193/0/0/NONE/0/0/-/- 0 0 p610:91:6:1:0
p 7 7 0 0 0 - NOP 0 _ 0 - _ 0 0 p0:0:0:0:0
p 8 8 0 0 0 - CMP 0 CONST/0/0/0/NONE/0/0/-/- 8193 - _ 0 0 p610:91:14:2:0
p 9 9 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/32/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p1:1:0:1:0
p 10 10 0 0 0 - CSEL 0 SPECIAL/0/0/0/NONE/0/129/-/- 8193 0:REG/8223/0/0/NONE/0/0/-/- REG/8192/0/0/NONE/0/0/-/- 0 0 p1:1:0:2:0
p 11 11 0 0 0 - RET 0 _ 0 - _ 0 0 p610:91:17:0:0
p 13 13 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 23 0 1 200091
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 0 MOVD MOVD
inlmark @9 470
funcaux y3 y4 - - y5 y6 -
needzero -
regargs -
text 0 0 - 0
symalign y3:4,y4:4,y5:1,y6:1
autot -
dbgentry 1
dbgslot 0 n4 t2 0
dbgslot 1 n1 t2 16
dbgslot 2 n1 t3 0
dbgslot 3 n1 t4 8
dbgvar 0 n1 2,3,1
dbgloc 0 1:-10000:1:11:509308519308529308,1:11:1:14:5093089308529308,1:14:-1:-30000:93089308529308
dbgregout n2
dbgpc 1:11:7,1:14:11
end
asm
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i24 0 2 p1:1:0:0:0
p 14 0 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/0/y2/- 0 0 p1:1:0:2:0
p 15 4 0 0 304 - MOVD 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/47/8/y2/- 0 0 p1:1:0:2:0
p 1 8 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p1:1:0:0:0
p 2 8 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p1:1:0:0:0
p 3 8 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p1:1:0:0:0
p 4 8 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y6/- 0 0 p1:1:0:0:0
p 5 8 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p1:1:0:2:0
p 12 8 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:1:0
p 6 12 0 0 53 - AND 0 CONST/0/0/0/NONE/17/96/-/- 8194 - REG/8193/0/0/NONE/2/0/-/- 0 0 p610:91:6:1:0
p 7 16 0 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p0:0:0:0:0
p 8 16 0 0 96 - CMP 0 CONST/0/0/0/NONE/16/0/-/- 8193 - NONE/0/0/0/NONE/1/0/-/- 0 0 p610:91:14:2:0
p 9 20 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/32/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 10 24 0 0 102 - CSEL 0 SPECIAL/0/0/0/NONE/11/129/-/- 8193 0:REG/8223/0/0/NONE/3/0/-/- REG/8192/0/0/NONE/2/0/-/- 0 0 p1:1:0:2:0
p 11 28 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p610:91:17:0:0
fn y1 24 0 23 0 1 2000d9
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 0 MOVD MOVD
inlmark @9 470
funcaux y3 y4 - - y5 y6 -
text 32 0 e00700f9e10b00f91f2003d541047b923f0000f1e1037bb220109f9ac0035fd6 0
pcln y12 y13 y14 y15 y8,y9,y10,y11 y3,y4,_,_,_,y5,y6
usedfiles 0,11
inltree 0 -1 p1:1:0:0:0 y7 "flag.ro" 20
data y3 Sxxx 0 4 8000 02000000020000000300 0
data y4 Sxxx 0 4 8000 0200000000000000 0
data y5 SDATA 9 1 8000 fe000808081008fdff 0
data y6 SDATA 2 1 8000 0000 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 0 1 28000 - 0
data y10 SRODATA 0 1 28000 - 0
data y11 SRODATA 5 1 28000 0002040600 0
data y12 SRODATA 3 1 28000 020800 0
data y13 SRODATA 9 1 28000 020316021502160100 0
data y14 SRODATA 12 1 28000 0403b40102b30102b4010100 0
data y15 SRODATA 9 1 28000 000302020102020100 0
end
dwarf
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
posbase p13 "reflect/value.go" 1 1 -1 11 "reflect/value.go" "reflect/value.go" 1 1
sym y20 "go:info.reflect.flag.ro$abstract" 0
sym y21 "go:info.go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }" 0
sym y22 "go:info.reflect.flag" 0
sym y23 "type:reflect.flag" 0
dwfn y16 y17 y18 - y19 "go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }.reflect.ro" 0:1 1 1 1 292
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwinlfn y7 y20
dwinldcl y7 "f" 0 p13:90:7:0:0
dwinldcl y7 "~r0" 0 p13:90:20:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "go.shape.struct { reflect.typ_ *internal/abi.Type; reflect.ptr unsafe.Pointer; reflect.flag }" 0 0 1 p13:90:7:0:0
dwname n3 1 0 0 1 0 0 0 0 - - "reflect.flag" 0 0 1 p610:90:7:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "reflect.flag" 0 0 1 p13:90:20:0:0
dwname n4 1 0 0 1 0 0 0 0 - - "reflect.flag" 0 0 1 p610:90:20:0:0
var 0 0 "f" 5 1 0 0 0 8 y21 "reflect/value.go" 90 7 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y22 "reflect/value.go" 90 20 0 1 0 0 -
scope 0 0 - 0,1
inlcall 0 470 0:1 y20 - 1 12:16,16:20,28:32 -
data y16 SDWARFFCN 153 0 0 04676f2e73686170652e737472756374207b207265666c6563742e7479705f202a696e7465726e616c2f6162692e547970653b207265666c6563742e70747220756e736166652e506f696e7465723b207265666c6563742e666c6167207d2e7265666c6563742e726f00000020019c012d6600005a00000000000000002e7e723000015a000000000009000000000000000001000000010000 7
reloc 0 0 R_USETYPE 0 y23
reloc 106 2 R_DWTXTADDR_U2 0 y1
reloc 117 4 R_DWARFSECREF 0 y21
reloc 121 4 R_DWARFSECREF 0 y17
reloc 132 4 R_DWARFSECREF 0 y22
reloc 138 4 R_DWARFSECREF 0 y20
reloc 142 4 R_DWARFSECREF 0 y18
data y17 SDWARFLOC 40 0 0 0100000400100950930851930852930804101c085093089308529308041c20079308930852930800 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y18 SDWARFRANGE 13 0 0 010000040c10041014041c2000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y19 SDWARFLINES 44 0 0 0009020000000000000000060f065f040c03d5003c063704010603aa7f330637040c0603d5003c0204000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded method (`GenG2.load`, as `gen-check`). -/
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

#eval match checkG25 lc ps bs g with
  | .ok (t, k) => s!"{t} {k.map fun (b, m) => (b, (List.range 64).filterMap fun r => (m.get r).map (r, ·))}"
  | .error e => e
#eval ((lc.ctx.f.block? 1).map (·.values.toList), (accessedVars lc).isEmpty, (homeSlots lc).isEmpty)

end GoFV.Proof.Witness.GenG25
