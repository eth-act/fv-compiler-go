import GoFV.Proof.Gen.G31
import GoFV.Proof.Witness.GenG13

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G31 of the genssa validator on `runtime.(*hexdumper).close`

`std/std/runtime/(*hexdumper).close,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`;
`runtime/hexdump.go`):

```go
func (h *hexdumper) close() {
	if h.nbuf > 0 {
		h.flushLine(h.buf[:h.nbuf])
	}
}
```

Block `b1` loads the byte `h.nbuf` (`v8 = MOVBUload`, `MOVBU 41(R0), R4`), copies it
(`v18 = MOVDreg v8`, `MOVD R4, R5`) and branches on it (`NZW v18`, `CBZW R5`) to `b3` (nonzero) or
`b2`. Block `b3` copies it again (`v22 = MOVDreg v8`, `MOVD R4, R2`) for the bounds check
`CMP $16, R2`. G29's table `uL` starts empty in every block, so it knows nothing before `v22`
(index 0 of `b3`), and `checkG32` rejects the function (`MOVDnop/MOVDreg: upper bits unknown`).
G31's table starts `b3` with `uIn lc 3 = tbl = [(5, 8, false), (4, 8, false)]`, the end of `b1`, its
only predecessor: `R5` and `R4` are zero-extended from 8 bits. `checkG31` accepts the function with
the PC table `tab` and the class table `kt`.

By compiled evaluation (`native_decide`; `g31_facts`), `stepLoc` runs `v22` from a state with the
byte `0x2a` in `R4` to `R2 = 0x2a` as a 64-bit integer, and `stepTermLoc` runs `b1`'s `NZW` from a
state with `0x2a` in `R4` (8 bits) and `R5` (32 bits) to `b3`. On a framed activation with
`G28Env`:

* `genG31_value_witness`: from a machine whose `X4` and `X5` are zero-extended from 8 bits (`UOKL`
  of `uL31 lc (uIn lc 3) blk3 0`, the table from `b1`), `g31_value` runs `MOVD R4, R2` (`v22`): the
  machine's whole `X2` is `0x2a`, and the table after `v22` gives the whole `X4 = 0x2a`;
* `genG31_term_witness`: from a machine at `b1`'s `CBZW` whose `X4` and `X5` are zero-extended from
  8 bits (`UOKL` of the table at `b1`'s end), `g31_term` runs to `b3` with `UOKL` of
  `uIn lc 3 = tbl`, which gives the whole `X5 = 0x2a` (`LocMatch` alone gives its low 32 bits).
-/

namespace GoFV.Proof.Witness.GenG31

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/(*hexdumper).close,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "(*hexdumper).close" 1 0 0
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
type t4 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t5 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t8 INT 8 8 0 comparable,named "int" "int"
type t7 STRUCT 8 8 0 comparable,named "hexdumpMarker" "runtime.hexdumpMarker" 1
field 0 "chars" t8 0 0
type t6 FUNC 8 8 8 hasptr,direct "func(uintptr, hexdumpMarker)" "func(uintptr, runtime.hexdumpMarker)" 0 2 0
field 0 "addr" t4 ? 0
field 1 "m" t7 ? 0
type t9 INT8 1 1 0 comparable,named "int8" "int8"
type t11 UINT8 1 1 0 comparable,named "byte" "uint8"
type t10 ARRAY 16 1 0 comparable "[16]byte" "[16]uint8" t11 16
type t3 STRUCT 64 8 24 hasptr,named "hexdumper" "runtime.hexdumper" 9
field 0 "addr" t4 0 0
field 1 "addrBytes" t5 8 0
field 2 "wordBytes" t5 9 0
field 3 "mark" t6 16 0
field 4 "ready" t9 24 0
field 5 "dataBuf" t10 25 0
field 6 "dataPos" t5 41 0
field 7 "dataSkip" t5 42 0
field 8 "toPos" t10 43 0
type t2 PTR 8 8 8 hasptr,direct,comparable "*hexdumper" "*runtime.hexdumper" t3
type t1 FUNC 8 8 8 hasptr,direct "method(*hexdumper) func()" "method(*runtime.hexdumper) func()" 1 0 0
field 0 "h" t2 ? 0
aux a2 sym "runtime.(*hexdumper).close" "runtime.(*hexdumper).close" 1 - 0 - - - - 0
posbase p130 "runtime/hexdump.go" 1 1 -1
aux a3 name "h" "h" PPARAM t2 0 1 used p130:111:7:0:0
aux a1 call "AuxCall{runtime.(*hexdumper).close}" a2 1 1 0 8 8 1 0
abiparam in 0 t2 a3 0 0
type t12 BOOL 1 1 0 comparable,named "bool" "bool"
type t13 INT16 2 2 0 comparable,named "int16" "int16"
type t14 INT32 4 4 0 comparable,named "int32" "int32"
type t15 INT64 8 8 0 comparable,named "int64" "int64"
type t16 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t17 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t18 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t19 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t20 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t21 UINT 8 8 0 comparable,named "uint" "uint"
type t22 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t23 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t5
type t24 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t14
type t25 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t17
type t26 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t8
type t27 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t4
type t28 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t19
type t29 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t20
type t30 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t23
type t31 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t32 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t33 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t34 SSA ? ? ? - "mem" ""
type t35 SSA ? ? ? - "flags" ""
type t36 SSA ? ? ? - "void" ""
type t37 SSA 16 8 ? - "int128" ""
type t38 RESULTS ? ? ? - "mem" "" 1 t34
type t39 PTR 8 8 8 hasptr,direct,comparable "**hexdumper" "**runtime.hexdumper" t2
type t40 PTR 8 8 8 hasptr,direct,comparable "*[16]byte" "*[16]uint8" t10
type t41 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t11
type t42 SLICE 24 8 8 hasptr "[]byte" "[]uint8" t11
aux a5 sym "runtime.(*hexdumper).flushLine" "runtime.(*hexdumper).flushLine" 1 - 0 - - - - 0
aux a4 call "AuxCall{runtime.(*hexdumper).flushLine}" a5 1 2 0 8 32 4 0
abiparam in 0 t2 - 0 0
abiparam in 1 t42 - 1,2,3 8
slot s1 a3 t2 0 - 0
f b1 t1 a1 37 7
typs Bool=t12,Int8=t9,Int16=t13,Int32=t14,Int64=t15,UInt8=t5,UInt16=t16,UInt32=t17,UInt64=t18,Int=t8,Float32=t19,Float64=t20,UInt=t21,Uintptr=t4,String=t22,BytePtr=t23,Int32Ptr=t24,UInt32Ptr=t25,IntPtr=t26,UintptrPtr=t27,Float32Ptr=t28,Float64Ptr=t29,BytePtrPtr=t30,Complex64=t31,Complex128=t32,UnsafePtr=t33,Mem=t34,Flags=t35,Void=t36,Int128=t37,ResultMem=t38
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v2 SP t4 0 - p0:0:0:0:0 1 -
v v3 SB t4 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t39 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p130:111:6:2:0 2 -
v v6 NilCheck t2 0 - p130:112:6:0:0 1 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 1 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v21 Const64 t8 0 - p0:0:0:0:0 4 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:0:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v11 Copy t2 0 - p130:113:27:2:0 3 v5
v v12 Copy t34 0 - p130:113:27:2:0 7 v1
v v13 NilCheck t2 0 - p130:113:27:0:0 1 v11,v12
v v14 OffPtr t23 41 - p130:113:27:0:0 1 v13
v v15 Load t5 0 - p130:113:27:0:0 1 v14,v12
v v16 NilCheck t2 0 - p130:113:16:0:0 1 v11,v12
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v16
v v18 NilCheck t40 0 - p130:113:24:0:0 1 v17,v12
v v19 Copy t41 0 - p130:113:24:2:0 1 v18
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 5 v15
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 If p130:113:16:0:0 1 0 - v26 b6:0,b7:0 b3:0
v v26 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v21,v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v24 Copy t34 0 - p130:113:24:2:0 1 v12
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v24
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v29 Sub64 t8 0 - p130:113:24:0:0 1 v22,v21
v v30 Sub64 t8 0 - p130:113:24:0:0 1 v20,v21
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v19,v29,v30
v v32 Copy t2 0 - p130:113:14:2:0 1 v11
v v33 Copy t34 0 - p130:113:14:2:0 1 v12
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v32,v31,v33
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b7 Exit p130:113:16:0:0 0 0 - v28 - b4:1
v v27 Copy t34 0 - p130:113:24:2:0 1 v12
v v28 PanicBounds t34 6 - p130:113:24:0:0 1 v21,v22,v27
names s1
named s1 v5,v11,v32
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v21,16=v20
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v2 SP t4 0 - p0:0:0:0:0 1 -
v v3 SB t4 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t39 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p130:111:6:2:0 2 -
v v6 NilCheck t2 0 - p130:112:6:1:0 1 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 1 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v21 Const64 t8 0 - p0:0:0:0:0 4 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v11 Copy t2 0 - p130:113:27:2:0 3 v5
v v12 Copy t34 0 - p130:113:27:2:0 7 v1
v v13 NilCheck t2 0 - p130:113:27:1:0 1 v11,v12
v v14 OffPtr t23 41 - p130:113:27:0:0 1 v13
v v15 Load t5 0 - p130:113:27:0:0 1 v14,v12
v v16 NilCheck t2 0 - p130:113:16:0:0 1 v11,v12
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v16
v v18 NilCheck t40 0 - p130:113:24:0:0 1 v17,v12
v v19 Copy t41 0 - p130:113:24:2:0 1 v18
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 5 v15
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 If p130:113:16:0:0 1 0 - v26 b6:0,b7:0 b3:0
v v26 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v21,v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v24 Copy t34 0 - p130:113:24:2:0 1 v12
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v24
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v29 Sub64 t8 0 - p130:113:24:0:0 1 v22,v21
v v30 Sub64 t8 0 - p130:113:24:0:0 1 v20,v21
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v19,v29,v30
v v32 Copy t2 0 - p130:113:14:2:0 1 v11
v v33 Copy t34 0 - p130:113:14:2:0 1 v12
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v32,v31,v33
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b7 Exit p130:113:16:0:0 0 0 - v28 - b4:1
v v27 Copy t34 0 - p130:113:24:2:0 1 v12
v v28 PanicBounds t34 6 - p130:113:24:0:0 1 v21,v22,v27
names s1
named s1 v5,v11,v32
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v21,16=v20
freev -
freeb -
cache postorder b2,b6,b7,b4,b5,b3,b1
cache linestarts 130:112:115
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 15 -
v v2 SP t4 0 - p0:0:0:0:0 1 -
v v3 SB t4 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t39 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p130:111:6:2:0 6 -
v v6 NilCheck t2 0 - p130:112:6:1:0 1 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 1 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v21 Const64 t8 0 - p0:0:0:0:0 4 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v11 Copy t2 0 - p130:113:27:2:0 0 v5
v v12 Copy t34 0 - p130:113:27:2:0 0 v1
v v13 NilCheck t2 0 - p130:113:27:1:0 1 v5,v1
v v14 OffPtr t23 41 - p130:113:27:0:0 1 v13
v v15 Load t5 0 - p130:113:27:0:0 1 v14,v1
v v16 NilCheck t2 0 - p130:113:16:0:0 1 v5,v1
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v16
v v18 NilCheck t40 0 - p130:113:24:0:0 2 v17,v1
v v19 Copy t41 0 - p130:113:24:2:0 0 v18
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 5 v15
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 If p130:113:16:0:0 1 0 - v26 b6:0,b7:0 b3:0
v v26 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v21,v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v24 Copy t34 0 - p130:113:24:2:0 0 v1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v29 Sub64 t8 0 - p130:113:24:0:0 1 v22,v21
v v30 Sub64 t8 0 - p130:113:24:0:0 1 v20,v21
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v29,v30
v v32 Copy t2 0 - p130:113:14:2:0 0 v5
v v33 Copy t34 0 - p130:113:14:2:0 0 v1
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b7 Exit p130:113:16:0:0 0 0 - v28 - b4:1
v v27 Copy t34 0 - p130:113:24:2:0 0 v1
v v28 PanicBounds t34 6 - p130:113:24:0:0 1 v21,v22,v1
names s1
named s1 v5,v5,v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v21,16=v20
freev -
freeb -
cache postorder b2,b6,b7,b4,b5,b3,b1
cache linestarts 130:112:115
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 10 -
v v5 Arg t2 0 a3 p130:111:6:2:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 1 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 1 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v21 Const64 t8 0 - p0:0:0:0:0 4 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v13 NilCheck t2 0 - p130:113:27:1:0 1 v5,v1
v v14 OffPtr t23 41 - p130:113:27:0:0 1 v13
v v15 Load t5 0 - p130:113:27:0:0 1 v14,v1
v v16 NilCheck t2 0 - p130:113:16:0:0 1 v5,v1
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v16
v v18 NilCheck t40 0 - p130:113:24:0:0 1 v17,v1
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 5 v15
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 If p130:113:16:0:0 1 0 - v26 b6:0,b7:0 b3:0
v v26 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v21,v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v29 Sub64 t8 0 - p130:113:24:0:0 1 v22,v21
v v30 Sub64 t8 0 - p130:113:24:0:0 1 v20,v21
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v29,v30
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b7 Exit p130:113:16:0:0 0 0 - v28 - b4:1
v v28 PanicBounds t34 6 - p130:113:24:0:0 1 v21,v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v21,16=v20
freev v27,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb -
cache postorder b2,b6,b7,b4,b5,b3,b1
cache linestarts 130:112:115
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 10 -
v v5 Arg t2 0 a3 p130:111:6:2:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 1 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 1 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v21 Const64 t8 0 - p0:0:0:0:0 4 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v13 NilCheck t2 0 - p130:113:27:1:0 1 v5,v1
v v14 OffPtr t23 41 - p130:113:27:0:0 1 v13
v v15 Load t5 0 - p130:113:27:0:0 1 v14,v1
v v16 NilCheck t2 0 - p130:113:16:0:0 1 v5,v1
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v16
v v18 NilCheck t40 0 - p130:113:24:0:0 1 v17,v1
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 5 v15
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 If p130:113:16:0:0 1 0 - v26 b6:0,b7:0 b3:0
v v26 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v21,v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v29 Sub64 t8 0 - p130:113:24:0:0 1 v22,v21
v v30 Sub64 t8 0 - p130:113:24:0:0 1 v20,v21
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v29,v30
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b7 Exit p130:113:16:0:0 0 0 - v28 - b4:1
v v28 PanicBounds t34 6 - p130:113:24:0:0 1 v21,v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v21,16=v20
freev v27,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb -
cache postorder b2,b6,b7,b4,b5,b3,b1
cache linestarts 130:112:115
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 10 -
v v5 Arg t2 0 a3 p130:111:6:2:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 1 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 1 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v21 Const64 t8 0 - p0:0:0:0:0 4 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v13 NilCheck t2 0 - p130:113:27:1:0 1 v5,v1
v v14 OffPtr t23 41 - p130:113:27:0:0 1 v13
v v15 Load t5 0 - p130:113:27:0:0 1 v14,v1
v v16 NilCheck t2 0 - p130:113:16:0:0 1 v5,v1
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v16
v v18 NilCheck t40 0 - p130:113:24:0:0 1 v17,v1
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 5 v15
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 If p130:113:16:0:0 1 0 - v26 b6:0,b7:0 b3:0
v v26 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v21,v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v29 Sub64 t8 0 - p130:113:24:0:0 1 v22,v21
v v30 Sub64 t8 0 - p130:113:24:0:0 1 v20,v21
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v29,v30
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b7 Exit p130:113:16:0:0 0 0 - v28 - b4:1
v v28 PanicBounds t34 6 - p130:113:24:0:0 1 v21,v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v21,16=v20
freev v27,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb -
cache postorder b2,b6,b7,b4,b5,b3,b1
cache linestarts 130:112:115
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 10 -
v v5 Arg t2 0 a3 p130:111:6:2:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 1 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 1 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v21 Const64 t8 0 - p0:0:0:0:0 4 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v13 NilCheck t2 0 - p130:113:27:1:0 1 v5,v1
v v14 OffPtr t23 41 - p130:113:27:0:0 1 v13
v v15 Load t5 0 - p130:113:27:0:0 1 v14,v1
v v16 NilCheck t2 0 - p130:113:16:0:0 1 v5,v1
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v16
v v18 NilCheck t40 0 - p130:113:24:0:0 1 v17,v1
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 5 v15
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 If p130:113:16:0:0 1 0 - v26 b6:0,b7:0 b3:0
v v26 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v21,v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v29 Sub64 t8 0 - p130:113:24:0:0 1 v22,v21
v v30 Sub64 t8 0 - p130:113:24:0:0 1 v20,v21
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v29,v30
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b7 Exit p130:113:16:0:0 0 0 - v28 - b4:1
v v28 PanicBounds t34 6 - p130:113:24:0:0 1 v21,v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v21,16=v20
freev v27,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb -
cache postorder b2,b6,b7,b4,b5,b3,b1
cache linestarts 130:112:115
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 10 -
v v5 Arg t2 0 a3 p130:111:6:2:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 1 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 1 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 2 -
v v21 Const64 t8 0 - p0:0:0:0:0 1 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v13 NilCheck t2 0 - p130:113:27:1:0 1 v5,v1
v v14 OffPtr t23 41 - p130:113:27:0:0 1 v13
v v15 Load t5 0 - p130:113:27:0:0 1 v14,v1
v v16 NilCheck t2 0 - p130:113:16:0:0 1 v5,v1
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v16
v v18 NilCheck t40 0 - p130:113:24:0:0 1 v17,v1
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 4 v15
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 First p130:113:16:0:0 1 0 - - b6:0,b7:0 b3:0
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v30 Const64 t8 16 - p130:113:24:0:0 1 -
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v22,v30
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b7 Exit p130:113:16:0:0 0 0 - v28 - b4:1
v v28 PanicBounds t34 6 - p130:113:24:0:0 1 v21,v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v21,16=v20
freev v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb -
cache postorder b2,b6,b7,b4,b5,b3,b1
cache linestarts 130:112:115
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 10 -
v v5 Arg t2 0 a3 p130:111:6:2:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 1 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 1 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v21 Const64 t8 0 - p0:0:0:0:0 1 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v13 NilCheck t2 0 - p130:113:27:1:0 1 v5,v1
v v14 OffPtr t23 41 - p130:113:27:0:0 1 v13
v v15 Load t5 0 - p130:113:27:0:0 1 v14,v1
v v16 NilCheck t2 0 - p130:113:16:0:0 1 v5,v1
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v16
v v18 NilCheck t40 0 - p130:113:24:0:0 1 v17,v1
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 4 v15
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 First p130:113:16:0:0 1 0 - - b6:0,b7:0 b3:0
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v30 Const64 t8 16 - p130:113:24:0:0 0 -
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v22,v20
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b7 Exit p130:113:16:0:0 0 0 - v28 - b4:1
v v28 PanicBounds t34 6 - p130:113:24:0:0 1 v21,v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v21,16=v20
freev v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb -
cache postorder b2,b6,b7,b4,b5,b3,b1
cache linestarts 130:112:115
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 9 -
v v5 Arg t2 0 a3 p130:111:6:2:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 1 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 1 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v13 NilCheck t2 0 - p130:113:27:1:0 1 v5,v1
v v14 OffPtr t23 41 - p130:113:27:0:0 1 v13
v v15 Load t5 0 - p130:113:27:0:0 1 v14,v1
v v16 NilCheck t2 0 - p130:113:16:0:0 1 v5,v1
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v16
v v18 NilCheck t40 0 - p130:113:24:0:0 1 v17,v1
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 3 v15
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 Plain p130:113:16:0:0 0 0 - - b6:0 b3:0
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v22,v20
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v28,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache linestarts 130:112:115
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 9 -
v v5 Arg t2 0 a3 p130:111:6:2:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 3 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 2 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v13 NilCheck t2 0 - p130:113:27:1:0 0 v5,v1
v v14 OffPtr t23 41 - p130:113:27:0:0 0 v6
v v15 Load t5 0 - p130:113:27:0:0 0 v7,v1
v v16 NilCheck t2 0 - p130:113:16:0:0 0 v5,v1
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v6
v v18 NilCheck t40 0 - p130:113:24:0:0 1 v17,v1
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 Plain p130:113:16:0:0 0 0 - - b6:0 b3:0
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v22,v20
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v28,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b4,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b3,b5:b3,b6:b4
cache sdom b1:-:b3:-:2:35,b2:b1:-:-:29:32,b3:b1:b5:b2:5:26,b4:b3:b6:-:14:23,b5:b3:-:b4:8:11,b6:b4:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 9 -
v v5 Arg t2 0 a3 p130:111:6:2:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 3 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 2 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v13 NilCheck t2 0 - p130:113:27:1:0 0 v5,v1
v v14 OffPtr t23 41 - p130:113:27:0:0 0 v6
v v15 Load t5 0 - p130:113:27:0:0 0 v7,v1
v v16 NilCheck t2 0 - p130:113:16:0:0 0 v5,v1
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v6
v v18 NilCheck t40 0 - p130:113:24:0:0 1 v17,v1
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 Plain p130:113:16:0:0 0 0 - - b6:0 b3:0
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v22,v20
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v28,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b4,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b3,b5:b3,b6:b4
cache sdom b1:-:b3:-:2:35,b2:b1:-:-:29:32,b3:b1:b5:b2:5:26,b4:b3:b6:-:14:23,b5:b3:-:b4:8:11,b6:b4:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 8 -
v v5 Arg t2 0 a3 p130:111:6:2:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v13 NilCheck t2 0 - p130:113:27:1:0 0 v5,v1
v v16 NilCheck t2 0 - p130:113:16:0:0 0 v5,v1
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v6
v v18 NilCheck t40 0 - p130:113:24:0:0 1 v17,v1
v v22 ZeroExt8to64 t8 0 - p130:113:24:0:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 Plain p130:113:16:0:0 0 0 - - b6:0 b3:0
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v22,v20
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v15,v14,v28,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b4,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b3,b5:b3,b6:b4
cache sdom b1:-:b3:-:2:35,b2:b1:-:-:29:32,b3:b1:b5:b2:5:26,b4:b3:b6:-:14:23,b5:b3:-:b4:8:11,b6:b4:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v5 Arg t2 0 a3 p130:111:6:2:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v6 NilCheck t2 0 - p130:112:6:1:0 4 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v13 Copy t2 0 - p130:113:27:1:0 0 v6
v v16 Copy t2 0 - p130:113:16:0:0 0 v6
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v6
v v18 Copy t40 0 - p130:113:24:0:0 1 v17
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 Plain p130:113:16:0:0 0 0 - - b6:0 b3:0
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v22,v20
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v15,v14,v28,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b4,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b3,b5:b3,b6:b4
cache sdom b1:-:b3:-:2:35,b2:b1:-:-:29:32,b3:b1:b5:b2:5:26,b4:b3:b6:-:14:23,b5:b3:-:b4:8:11,b6:b4:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 Arg t2 0 a3 p130:111:6:2:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 4 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v13 Copy t2 0 - p130:113:27:1:0 0 v6
v v16 Copy t2 0 - p130:113:16:0:0 0 v6
v v17 OffPtr t40 25 - p130:113:16:0:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v18 Copy t40 0 - p130:113:24:0:0 1 v17
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 Plain p130:113:16:0:0 0 0 - - b6:0 b3:0
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v18,v22,v20
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v15,v14,v28,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b4,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b3,b5:b3,b6:b4
cache sdom b1:-:b3:-:2:35,b2:b1:-:-:29:32,b3:b1:b5:b2:5:26,b4:b3:b6:-:14:23,b5:b3:-:b4:8:11,b6:b4:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 Arg t2 0 a3 p130:111:6:2:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 Plain p130:113:16:0:0 0 0 - - b6:0 b3:0
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v17,v22,v20
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v18,v16,v13,v15,v14,v28,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b4,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b3,b5:b3,b6:b4
cache sdom b1:-:b3:-:2:35,b2:b1:-:-:29:32,b3:b1:b5:b2:5:26,b4:b3:b6:-:14:23,b5:b3:-:b4:8:11,b6:b4:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 Arg t2 0 a3 p130:111:6:2:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 Plain p130:113:16:0:0 0 0 - - b6:0 b3:0
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v17,v22,v20
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v18,v16,v13,v15,v14,v28,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b4,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b3,b5:b3,b6:b4
cache sdom b1:-:b3:-:2:35,b2:b1:-:-:29:32,b3:b1:b5:b2:5:26,b4:b3:b6:-:14:23,b5:b3:-:b4:8:11,b6:b4:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 Arg t2 0 a3 p130:111:6:2:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 Plain p130:113:16:0:0 0 0 - - b6:0 b3:0
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v17,v22,v20
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v18,v16,v13,v15,v14,v28,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b4,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b3,b5:b3,b6:b4
cache sdom b1:-:b3:-:2:35,b2:b1:-:-:29:32,b3:b1:b5:b2:5:26,b4:b3:b6:-:14:23,b5:b3:-:b4:8:11,b6:b4:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 Arg t2 0 a3 p130:111:6:2:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b4:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 Plain p130:113:16:0:0 0 0 - - b6:0 b3:0
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b4:0
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v17,v22,v20
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v18,v16,v13,v15,v14,v28,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b4,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b3,b5:b3,b6:b4
cache sdom b1:-:b3:-:2:35,b2:b1:-:-:29:32,b3:b1:b5:b2:5:26,b4:b3:b6:-:14:23,b5:b3:-:b4:8:11,b6:b4:-:-:17:20
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 Arg t2 0 a3 p130:111:6:2:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 BlockInvalid p130:113:16:0:0 0 0 - - - -
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v31 SliceMake t42 0 - p130:113:24:0:0 1 v17,v22,v20
v v34 StaticLECall t38 32 a4 p130:113:14:0:0 1 v5,v31,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v18,v16,v13,v15,v14,v28,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 20 "expand calls"
aux a6 nameoff "h+0" a3 0
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v18 SB t4 0 - p0:0:0:0:0 0 -
v v16 SP t4 0 - p0:0:0:0:0 1 -
v v13 OffPtr t39 0 - p0:0:0:0:0 0 v16
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 BlockInvalid p130:113:16:0:0 0 0 - - - -
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v31 SliceMake t42 0 - p130:113:24:0:0 3 v17,v22,v20
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v15,v14,v28,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
v v15 SlicePtr t41 0 - p130:113:14:0:0 1 v31
v v14 SliceLen t8 0 - p130:113:14:2:0 1 v31
v v28 SliceCap t8 0 - p130:113:14:2:0 1 v31
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v13,16=v20
freev v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 21 "decompose builtin"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v18 SB t4 0 - p0:0:0:0:0 0 -
v v16 SP t4 0 - p0:0:0:0:0 1 -
v v13 OffPtr t39 0 - p0:0:0:0:0 0 v16
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 2 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 4 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 BlockInvalid p130:113:16:0:0 0 0 - - - -
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v31 SliceMake t42 0 - p130:113:24:0:0 0 v17,v22,v20
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v13,16=v20
freev v28,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v18 SB t4 0 - p0:0:0:0:0 0 -
v v16 SP t4 0 - p0:0:0:0:0 1 -
v v13 OffPtr t39 0 - p0:0:0:0:0 0 v16
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 2 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 4 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 BlockInvalid p130:113:16:0:0 0 0 - - - -
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v31 SliceMake t42 0 - p130:113:24:0:0 0 v17,v22,v20
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v13,16=v20
freev v28,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 4 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
v v18 SB t4 0 - p0:0:0:0:0 0 -
v v16 SP t4 0 - p0:0:0:0:0 1 -
v v13 OffPtr t39 0 - p0:0:0:0:0 0 v16
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 2 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 4 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 BlockInvalid p130:113:16:0:0 0 0 - - - -
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v31 SliceMake t42 0 - p130:113:24:0:0 0 v17,v22,v20
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,v13,16=v20
freev v28,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 BlockInvalid p130:113:16:0:0 0 0 - - - -
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v31,v13,v16,v18,v28,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 BlockInvalid p130:113:16:0:0 0 0 - - - -
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v31,v13,v16,v18,v28,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b4 BlockInvalid p130:113:16:0:0 0 0 - - - -
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v31,v13,v16,v18,v28,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v31,v13,v16,v18,v28,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v31,v13,v16,v18,v28,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v31,v13,v16,v18,v28,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v31,v13,v16,v18,v28,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v31,v13,v16,v18,v28,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 37 7
b b1 If p130:112:17:0:0 0 0 - v10 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v9 Const8 t5 0 - p0:0:0:0:0 1 -
v v20 Const64 t8 16 - p0:0:0:0:0 3 -
v v6 NilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v7 OffPtr t23 41 - p130:112:6:0:0 1 v6
v v8 Load t5 0 - p130:112:6:0:0 2 v7,v1
v v10 Less8U t12 0 - p130:112:15:0:0 1 v9,v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 If p130:113:16:0:0 1 0 - v23 b6:0,b5:0 b1:0
v v17 OffPtr t40 25 - p130:113:16:1:0 1 v6
v v22 ZeroExt8to64 t8 0 - p130:113:24:1:0 3 v8
v v23 IsSliceInBounds t12 0 - p130:113:24:0:0 1 v22,v20
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 PanicBounds t34 2 - p130:113:24:0:0 1 v22,v20,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 StaticCall t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v9,16=v20
freev v31,v13,v16,v18,v28,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 33 "lower"
aux a7 pbc "{16}" 16
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
v v18 ARM64MOVBUreg t17 0 - p130:112:15:0:0 1 v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
v v22 ARM64MOVBUreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
v v18 ARM64MOVBUreg t17 0 - p130:112:15:0:0 1 v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
v v22 ARM64MOVBUreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 36 "pair"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache auxmap a3:1,-:2
cache linestarts 130:112:115
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b3,b6:b3
cache sdom b1:-:b3:-:2:29,b2:b1:-:-:23:26,b3:b1:b5:b2:5:20,b5:b3:-:b6:8:11,b6:b3:-:-:14:17
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b3,b6:b3
cache sdom b1:-:b3:-:2:29,b2:b1:-:-:23:26,b3:b1:b5:b2:5:20,b5:b3:-:b6:8:11,b6:b3:-:-:14:17
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b3,b6:b3
cache sdom b1:-:b3:-:2:29,b2:b1:-:-:23:26,b3:b1:b5:b2:5:20,b5:b3:-:b6:8:11,b6:b3:-:-:14:17
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b3,b6:b3
cache sdom b1:-:b3:-:2:29,b2:b1:-:-:23:26,b3:b1:b5:b2:5:20,b5:b3:-:b6:8:11,b6:b3:-:-:14:17
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b3,b6:b3
cache sdom b1:-:b3:-:2:29,b2:b1:-:-:23:26,b3:b1:b5:b2:5:20,b5:b3:-:b6:8:11,b6:b3:-:-:14:17
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b3,b6:b3
cache sdom b1:-:b3:-:2:29,b2:b1:-:-:23:26,b3:b1:b5:b2:5:20,b5:b3:-:b6:8:11,b6:b3:-:-:14:17
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b3,b6:b3
cache sdom b1:-:b3:-:2:29,b2:b1:-:-:23:26,b3:b1:b5:b2:5:20,b5:b3:-:b6:8:11,b6:b3:-:-:14:17
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b3,b6:b3
cache sdom b1:-:b3:-:2:29,b2:b1:-:-:23:26,b3:b1:b5:b2:5:20,b5:b3:-:b6:8:11,b6:b3:-:-:14:17
cache loopnest 8 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b4,b7
cache postorder b2,b6,b5,b3,b1
cache idom b1:-,b2:b1,b3:b1,b5:b3,b6:b3
cache sdom b1:-:b3:-:2:29,b2:b1:-:-:23:26,b3:b1:b5:b2:5:20,b5:b3:-:b6:8:11,b6:b3:-:-:14:17
cache loopnest 8 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b4:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
b b2 Ret p130:115:1:0:0 0 0 - v37 - b4:0,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
b b4 Plain p130:112:17:0:0 0 0 - - b2:0 b1:1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b4:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
b b2 Ret p130:115:1:0:0 0 0 - v37 - b4:0,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
b b4 Plain p130:112:17:0:0 0 0 - - b2:0 b1:1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b4:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
b b2 Ret p130:115:1:0:0 0 0 - v37 - b4:0,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
b b4 Plain p130:112:17:0:0 0 0 - - b2:0 b1:1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b5,b3,b4,b1
cache idom b1:-,b2:b1,b3:b1,b5:b3,b6:b3,b4:b1
cache sdom b1:-:b4:-:2:35,b2:b1:-:-:29:32,b3:b1:b5:b2:11:26,b5:b3:-:b6:14:17,b6:b3:-:-:20:23,b4:b1:-:b3:5:8
cache loopnest 8 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b4:0 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 2 -
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
v v6 ARM64LoweredNilCheck t2 0 - p130:112:6:1:0 2 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v6,v1
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v6
b b4 Plain p130:112:17:0:0 0 0 - - b2:0 b1:1
b b2 Ret p130:115:1:0:0 0 0 - v37 - b4:0,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b5,b3,b4,b1
cache idom b1:-,b3:b1,b6:b3,b4:b1,b2:b1,b5:b3
cache sdom b1:-:b4:-:2:35,b3:b1:b5:b2:11:26,b6:b3:-:-:20:23,b4:b1:-:b3:5:8,b2:b1:-:-:29:32,b5:b3:-:b6:14:17
cache loopnest 8 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b4:0 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 4 -
v v1 InitMem t34 0 - p0:0:0:0:0 5 -
v v6 ARM64LoweredNilCheck t36 0 - p130:112:6:1:0 0 v5,v1
v v8 ARM64MOVBUload t5 41 - p130:112:6:0:0 2 v5,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v5
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b4 Plain p130:112:17:0:0 0 0 - - b2:0 b1:1
b b2 Ret p130:115:1:0:0 0 0 - v37 - b4:0,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b5,b3,b4,b1
cache idom b1:-,b3:b1,b6:b3,b4:b1,b2:b1,b5:b3
cache sdom b1:-:b4:-:2:35,b3:b1:b5:b2:11:26,b6:b3:-:-:20:23,b4:b1:-:b3:5:8,b2:b1:-:-:29:32,b5:b3:-:b6:14:17
cache loopnest 8 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b4:0 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 3 -
v v1 InitMem t34 0 - p0:0:0:0:0 4 -
v v8 ARM64MOVBUload t5 41 - p130:112:6:1:0 2 v5,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v5
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b4 Plain p130:112:17:0:0 0 0 - - b2:0 b1:1
b b2 Ret p130:115:1:0:0 0 0 - v37 - b4:0,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b5,b3,b4,b1
cache idom b1:-,b3:b1,b6:b3,b4:b1,b2:b1,b5:b3
cache sdom b1:-:b4:-:2:35,b3:b1:b5:b2:11:26,b6:b3:-:-:20:23,b4:b1:-:b3:5:8,b2:b1:-:-:29:32,b5:b3:-:b6:14:17
cache loopnest 8 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b4:0 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 3 -
v v1 InitMem t34 0 - p0:0:0:0:0 4 -
v v8 ARM64MOVBUload t5 41 - p130:112:6:1:0 2 v5,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v20 ARM64MOVDconst t8 16 - p0:0:0:0:0 1 -
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v5
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v20,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b4 Plain p130:112:17:0:0 0 0 - - b2:0 b1:1
b b2 Ret p130:115:1:0:0 0 0 - v37 - b4:0,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v23,v28,v16,v13,v10,v7,v9,v14,v15,v30,v21,v27,v29,v26,v33,v32,v24,v19,v12,v11,v4,v3,v2
freeb b7
cache postorder b2,b6,b5,b3,b4,b1
cache idom b1:-,b3:b1,b6:b3,b4:b1,b2:b1,b5:b3
cache sdom b1:-:b4:-:2:35,b3:b1:b5:b2:11:26,b6:b3:-:-:20:23,b4:b1:-:b3:5:8,b2:b1:-:-:29:32,b5:b3:-:b6:14:17
cache loopnest 8 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a4 call "AuxCall{runtime.(*hexdumper).flushLine}" a5 1 2 0 8 32 4 0
abiparam in 0 t2 - 0 0
abiparam in 1 t42 - 1,2,3 8
callreg 0:1,1:2,2:4,3:8 - 7fffffff97ffffff -
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b4:0 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 3 -
v v1 InitMem t34 0 - p0:0:0:0:0 4 -
v v8 ARM64MOVBUload t5 41 - p130:112:6:1:0 2 v5,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v5
v v23 ARM64MOVDconst t8 16 - p130:113:14:2:0 1 -
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v23,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b4 Plain p130:112:17:0:0 0 0 - - b2:0 b1:1
b b2 Ret p130:115:1:0:0 0 0 - v37 - b4:0,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v7,v9,v10,v11,v12,v13,v14,v15,v16,v19,v21,v24,v26,v27,v28,v29,v30,v32,v33
freeb b7
cache postorder b2,b6,b5,b3,b4,b1
cache idom b1:-,b3:b1,b6:b3,b4:b1,b2:b1,b5:b3
cache sdom b1:-:b4:-:2:35,b3:b1:b5:b2:11:26,b6:b3:-:-:20:23,b4:b1:-:b3:5:8,b2:b1:-:-:29:32,b5:b3:-:b6:14:17
cache loopnest 8 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
fstate scheduled,laidout
regalloc 35 v5:R0,v8:R4,v17:R1,v18:R5,v22:R2,v23:R3,v34:[]
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b4:0 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 3 -
v v1 InitMem t34 0 - p0:0:0:0:0 4 -
v v8 ARM64MOVBUload t5 41 - p130:112:6:1:0 2 v5,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v5
v v23 ARM64MOVDconst t8 16 - p130:113:14:2:0 1 -
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v23,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b4 Plain p130:112:17:0:0 0 0 - - b2:0 b1:1
b b2 Ret p130:115:1:0:0 0 0 - v37 - b4:0,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v7,v9,v10,v11,v12,v13,v14,v15,v16,v19,v21,v24,v26,v27,v28,v29,v30,v32,v33
freeb b7
cache postorder b2,b6,b5,b3,b4,b1
cache idom b1:-,b3:b1,b6:b3,b4:b1,b2:b1,b5:b3
cache sdom b1:-:b4:-:2:35,b3:b1:b5:b2:11:26,b6:b3:-:-:20:23,b4:b1:-:b3:5:8,b2:b1:-:-:29:32,b5:b3:-:b6:14:17
cache loopnest 8 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
fstate scheduled,laidout
regalloc 35 v5:R0,v8:R4,v17:R1,v18:R5,v22:R2,v23:R3,v34:[]
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 37 7
b b1 ARM64NZW p130:112:17:0:0 0 0 - v18 b3:0,b2:0 -
v v5 ArgIntReg t2 0 a6 p130:112:17:0:0 3 -
v v1 InitMem t34 0 - p0:0:0:0:0 4 -
v v8 ARM64MOVBUload t5 41 - p130:112:6:1:0 2 v5,v1
v v18 ARM64MOVDreg t17 0 - p130:112:15:0:0 1 v8
b b3 ARM64ULE p130:113:16:0:0 1 0 - v31 b6:0,b5:0 b1:0
v v22 ARM64MOVDreg t8 0 - p130:113:24:1:0 3 v8
v v31 ARM64CMPconst t35 16 - p130:113:24:0:0 1 v22
b b6 Plain p130:113:14:0:0 0 0 - - b2:1 b3:0
v v17 ARM64ADDconst t40 25 - p130:113:16:1:0 1 v5
v v23 ARM64MOVDconst t8 16 - p130:113:14:2:0 1 -
v v34 ARM64CALLstatic t38 32 a4 p130:113:14:0:0 1 v5,v17,v22,v23,v1
v v35 SelectN t34 0 - p130:113:14:0:0 1 v34
b b2 Ret p130:115:1:0:0 0 0 - v37 - b1:1,b6:0
v v36 Phi t34 0 - p130:115:1:0:0 1 v1,v35
v v37 MakeResult t38 0 - p130:115:1:1:0 1 v36
b b5 Exit p130:113:16:0:0 0 0 - v25 - b3:1
v v25 ARM64LoweredPanicBoundsRC t34 2 a7 p130:113:24:0:0 1 v22,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v7,v9,v10,v11,v12,v13,v14,v15,v16,v19,v21,v24,v26,v27,v28,v29,v30,v32,v33
freeb b7
cache auxmap a3:1,-:2,a6:3
cache linestarts 130:112:115
fstate scheduled,laidout
regalloc 35 v5:R0,v8:R4,v17:R1,v18:R5,v22:R2,v23:R3,v34:[]
dcllen 3
end
frontend
end
ptrcache t3,t4,t5,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t27,t30,t31,t32,t33,t41,t42
typelink t5=t11,t23=t41,t34=t38
typeorder t9,t5=t11,t13,t16,t14,t17,t15,t18,t8,t21,t4,t31,t32,t19,t20,t12,t23=t41,t24,t25,t26,t27,t28,t29,t30,t39,t40,t2,t6,t1,t42,t10,t3,t7,t22,t33,t34,t36,t35,t37,t38
eof
"#

/-- `std/std/runtime/(*hexdumper).close,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "(*hexdumper).close" 1
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
type t1 8 8 8 1 01 "*hexdumper"
name n1 "h" PPARAM t1 1 "runtime.h" 0 a3
type t2 1 1 0 0 - "uint8"
name n2 ".autotmp_1" PAUTO t2 3 "runtime..autotmp_1" 0 -
type t3 24 8 8 1 01 "[]byte"
name n3 ".autotmp_2" PAUTO t3 3 "runtime..autotmp_2" 0 -
in n1 0 used
in n2 0 used,autotmp
in n3 0 used,autotmp
out n1 0 used
opt n3 0 autotmp
opt n2 0 autotmp
stack 0 0 8
end
genin
posbase p130 "runtime/hexdump.go" 1 1 -1 127 "runtime/hexdump.go" "runtime/hexdump.go" 1 1
sym y1 "runtime.(*hexdumper).close" 1
curfn p130:111:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 111 201080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.(*hexdumper).close.arginfo1" 0
sym y5 "runtime.(*hexdumper).close.argliveinfo" 0
sym y6 "runtime.(*hexdumper).flushLine" 1
sym y7 "runtime.panicBounds" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i8 0 0 p130:111:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p130:111:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p130:111:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p130:111:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p130:111:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p130:111:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p130:112:6:1:0
p 7 7 0 0 0 - MOVBU 0 MEM/8192/0/0/NONE/0/41/-/- 0 - REG/8196/0/0/NONE/0/0/-/- 0 0 p130:112:6:1:0
p 8 8 0 0 0 - MOVD 0 REG/8196/0/0/NONE/0/0/-/- 0 - REG/8197/0/0/NONE/0/0/-/- 0 0 p130:112:15:2:0
p 9 9 0 0 0 - CBZW 0 REG/8197/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@17 0 0 p130:112:17:2:0
p 10 10 0 0 0 - MOVD 0 REG/8196/0/0/NONE/0/0/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p130:113:24:1:0
p 11 11 0 0 0 - CMP 0 CONST/0/0/0/NONE/0/16/-/- 8194 - _ 0 0 p130:113:24:2:0
p 12 12 0 0 0 - BHI 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@18 0 0 p130:113:16:2:0
p 13 13 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/25/-/- 8192 - REG/8193/0/0/NONE/0/0/-/- 0 0 p130:113:16:1:0
p 14 14 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/16/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p130:113:14:2:0
p 15 15 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p130:113:14:2:0
p 16 16 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p130:113:14:2:0
p 17 17 0 0 0 - RET 0 _ 0 - _ 0 0 p130:115:1:0:0
p 18 18 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/4/-/- 0 - CONST/0/0/0/NONE/0/18622/-/- 0 0 p130:113:24:2:0
p 19 19 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p130:113:24:2:0
p 20 20 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p130:113:16:0:0
p 21 21 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 111 201080
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
dbgloc 0 1:-10000:6:34:50
dbgregout -
dbgpc 6:34:17
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
sym y17 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/48/-/i8 0 0 p130:111:6:0:0
p 22 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p130:111:6:0:0
p 23 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p130:111:6:0:0
p 24 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p130:111:6:0:0
p 25 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@34 0 0 p130:111:6:0:0
p 26 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p130:111:6:0:0
p 27 12 48 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-48/-/- 0 0 p130:111:6:0:1
p 28 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p130:111:6:0:0
p 29 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p130:111:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p130:111:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p130:111:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p130:111:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p130:111:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p130:111:6:2:0
p 6 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p130:112:6:1:0
p 7 24 0 0 294 - MOVBU 0 MEM/8192/0/0/NONE/89/41/-/- 0 - REG/8196/0/0/NONE/2/0/-/- 0 0 p130:112:6:1:0
p 8 28 0 0 301 - MOVD 0 REG/8196/0/0/NONE/2/0/-/- 0 - REG/8197/0/0/NONE/2/0/-/- 0 0 p130:112:15:2:0
p 9 32 0 0 85 - CBZW 0 REG/8197/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/17/-/@17 0 0 p130:112:17:2:0
p 10 36 0 0 301 - MOVD 0 REG/8196/0/0/NONE/2/0/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p130:113:24:1:0
p 11 40 0 0 96 - CMP 0 CONST/0/0/0/NONE/17/16/-/- 8194 - NONE/0/0/0/NONE/1/0/-/- 0 0 p130:113:24:2:0
p 12 44 0 0 80 - BHI 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/18/-/@18 0 0 p130:113:16:2:0
p 13 48 0 0 31 - ADD 0 CONST/0/0/0/NONE/18/25/-/- 8192 - REG/8193/0/0/NONE/2/0/-/- 0 0 p130:113:16:1:0
p 14 52 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/16/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p130:113:14:2:0
p 15 56 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p130:113:14:2:0
p 16 56 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y6/- 0 0 p130:113:14:2:0
p 17 60 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p130:115:1:0:0
p 30 64 -48 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/48/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p130:115:1:0:0
p 31 68 48 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p130:115:1:0:0
p 18 72 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/4/-/- 0 - CONST/0/0/0/NONE/23/18622/-/- 0 0 p130:113:24:2:0
p 19 72 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y7/- 0 0 p130:113:24:2:0
p 20 76 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p130:113:16:0:0
p 32 80 -48 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p130:113:16:0:0
p 33 80 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p130:111:6:0:0
p 34 80 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p130:111:6:0:0
p 35 80 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p130:111:6:0:0
p 36 84 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p130:111:6:0:0
p 37 88 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y8/- 0 0 p130:111:6:0:0
p 38 92 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p130:111:6:0:0
p 39 92 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p130:111:6:0:0
p 40 96 48 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@22 0 0 p130:111:6:0:0
fn y1 8 40 0 0 111 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 112 0 900b40f9ff6330eb49020054fe0f1df8fd831ff8fd2300d104a44039e50304aae5000034e20304aa5f4000f1e800005401640091e3037cb200000094fd835ff8fe0743f8c0035fd6000000941f2003d5e00700f9e3031eaa00000094e00740f9e8ffff17000000000000000000000000 3
reloc 56 4 R_CALLARM64 0 y6
reloc 72 4 R_CALLARM64 0 y7
reloc 88 4 R_CALLARM64 0 y8
pcln y14 y15 y16 y17 y9,y10,y11,y12,y13 y2,y3,_,_,_,y4,y5
usedfiles 127
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y9 SRODATA 11 1 28000 0001010202030111020500 0
data y10 SRODATA 7 1 28000 000e0406030800 0
data y11 SRODATA 0 1 28000 - 0
data y12 SRODATA 5 1 28000 0006041600 0
data y13 SRODATA 7 1 28000 0012fea2020a00 0
data y14 SRODATA 11 1 28000 0204600d5f0160025f0800 0
data y15 SRODATA 4 1 28000 80021c00 0
data y16 SRODATA 14 1 28000 e001060203020604030302030800 0
data y17 SRODATA 3 1 28000 001c00 0
end
dwarf
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
sym y21 "go:info.runtime.(*hexdumper).close$abstract" 0
sym y22 "" 0
sym y23 "go:info.*runtime.hexdumper" 0
dwfn y18 y19 y20 y21 y22 "runtime.(*hexdumper).close" 127:111 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwprecursor y1 y21 n1
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime.hexdumper" 0 0 1 p130:111:7:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "[]uint8" 0 0 1 p130:113:24:0:0
dwname n2 1 0 1 0 0 0 0 0 - - "uint8" 0 0 1 p130:113:24:0:0
var 0 0 "h" 5 1 0 0 0 8 y23 "runtime/hexdump.go" 111 7 0 0 1 0 v0
scope 0 0 - 0
dieref y18 2 y21 0
dieoff y21 0:31
data y18 SDWARFFCN 20 0 0 0600000000000070019c29000000000000000000 4
reloc 1 4 R_DWARFSECREF 0 y21
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y21
reloc 15 4 R_DWARFSECREF 0 y19
data y19 SDWARFLOC 9 0 0 01000004003c015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y20 SDWARFRANGE 0 0 0 - 0
data y22 SDWARFLINES 43 0 0 000902000000000000000004800103e900140a8788063706600637065f0637066106850637350220000101 1
reloc 3 8 R_ADDR 0 y1
data y21 SDWARFABSFCN 40 0 1 0572756e74696d652e282a68657864756d706572292e636c6f736500016f01226800000000000000 1
reloc 35 4 R_DWARFSECREF 0 y23
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

/-- The PC table `checkG31` gives (`b1`, `b3`, `b6`, `b2`, `b5`: one entry per value, then the
terminator). -/
def tab : PcTab := [(1, [5, 5, 5, 8, 9]), (3, [10, 11, 12]), (6, [13, 14, 15, 17, 17]),
  (2, [17, 17, 17]), (5, [18, 20])]

/-- The class table `checkG31` gives. -/
def kt : KTab := (match checkG31 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk1 : Block := (lc.ctx.f.block? 1).getD default

def blk3 : Block := (lc.ctx.f.block? 3).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG31`. -/
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

/-- The table at the end of `b1` and at the start of `b3` (`uIn lc 3`): `R5` (`v18`) and `R4`
(`v8`) zero-extended from 8 bits. -/
def tbl : List (Nat × Nat × Bool) := [(5, 8, false), (4, 8, false)]

/-- The table after `v22`: `R2` (`v22`) too. -/
def tbl1 : List (Nat × Nat × Bool) := [(2, 8, false), (5, 8, false), (4, 8, false)]

/-- The `runLoc` state before `v22`: the byte `0x2a` (`h.nbuf`, `v8`) in `R4`, every other register
`poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 4 then .int .w8 0x2a else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v22`: `X4 = 0x2a` and `X5 = 0`, both zero-extended from 8 bits, the
activation's `g` and `FP`, the PC of `v22`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 4 then 0x2a else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 3 0, mem := fun _ => 0 }

/-- The `runLoc` state at `b1`'s terminator: the byte `0x2a` in `R4` (`v8`) and as a 32-bit integer
in `R5` (`v18`), every other register `poison`, the empty memory. -/
def sT : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 4 then .int .w8 0x2a else if i.val = 5 then .int .w32 0x2a else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine at `b1`'s `CBZW R5`: `X4 = X5 = 0x2a`, the activation's `g` and `FP`, a zero
memory. -/
def mT : MState :=
  { x := fun k => if k = 4 then 0x2a else if k = 5 then 0x2a else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 4, mem := fun _ => 0 }

/-- The register holds the 64-bit integer `0x2a`. -/
def isW64 : Option Val → Bool
  | some (.int .w64 x) => x == 0x2a
  | _ => false

theorem isW64_spec {o : Option Val} (h : isW64 o = true) : o = some (.int .w64 0x2a) := by
  unfold isW64 at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- The register holds the 32-bit integer `0x2a`. -/
def isW32 : Option Val → Bool
  | some (.int .w32 x) => x == 0x2a
  | _ => false

theorem isW32_spec {o : Option Val} (h : isW32 o = true) : o = some (.int .w32 0x2a) := by
  unfold isW32 at h
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

/-- What compiled evaluation checks on `(*hexdumper).close`, for `v22`: it holds an arm64 op,
`checkG31` accepts it with `tab` and `kt` and `checkG32` does not; it accesses no frame variable
and has no home slot; `b3` holds `v22` (`MOVDreg v8`) at index 0; `R4` has class 8 before it;
G29's table `uL` is empty there, while `uIn lc 3` and G31's `uL31` before `v22` are `tbl`, and
`tbl1` after it; `stepLoc` runs `v22` from `s0` to `R2 = 0x2a` (64 bits), keeping `R4 = 0x2a`
(8 bits). -/
def gFactsV : Bool :=
  lc.ctx.f.lowered &&
    (checkG31 lc ps bs g).toOption == some (tab, kt) && (checkG32 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 3 && (lc.ctx.f.block? 3).isSome &&
    (lc.ctx.f.value? 22).isSome && blk3.values[0]? == some 22 &&
    (val 22).op == .ARM64MOVDreg && (val 22).args == #[8] &&
    (kAt lc kt 3 blk3 0).get 4 == some 8 &&
    uL lc blk3 0 == [] && uIn lc 3 == tbl && uL31 lc (uIn lc 3) blk3 0 == tbl &&
    uL31 lc (uIn lc 3) blk3 1 == tbl1 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 22)) fun s1 => isW64 s1.regs[2]? && isW8 s1.regs[4]?

/-- What compiled evaluation checks on `(*hexdumper).close`, for `b1`'s terminator: `b1` is the
entry (`uIn lc 1 = []`), holds four values and ends in `NZW`; `R4` has class 8 and `R5` class 32
at its end, where `uL31` is `tbl`; `stepTermLoc` runs it from `sT` to `b3`, keeping
`R5 = 0x2a` (32 bits). -/
def gFactsT : Bool :=
  lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    blk1.values.size == 4 && blk1.kind == .ARM64NZW &&
    (kAt lc kt 1 blk1 4).get 4 == some 8 && (kAt lc kt 1 blk1 4).get 5 == some 32 &&
    uIn lc 1 == [] && uL31 lc (uIn lc 1) blk1 4 == tbl &&
    GenG1.okThen (stepTermLoc lc sT blk1) fun r => GenG1.gotoIs r.1 3 && isW32 r.2.regs[5]?

def gFacts : Bool := gFactsV && gFactsT

theorem g31_facts : gFacts = true := by
  native_decide

/-- The facts of `gFactsV` as hypotheses. -/
theorem factsV :
    lc.ctx.f.lowered = true ∧ checkG31 lc ps bs g = .ok (tab, kt) ∧
      (checkG32 lc ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      3 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 3 = some blk3 ∧
      lc.ctx.f.value? 22 = some (val 22) ∧ blk3.values[0]? = some 22 ∧
      (val 22).op = .ARM64MOVDreg ∧ (val 22).args = #[8] ∧
      (kAt lc kt 3 blk3 0).get 4 = some 8 ∧
      uL lc blk3 0 = [] ∧ uIn lc 3 = tbl ∧ uL31 lc (uIn lc 3) blk3 0 = tbl ∧
      uL31 lc (uIn lc 3) blk3 1 = tbl1 ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 22))
        (fun s1 => isW64 s1.regs[2]? && isW8 s1.regs[4]?) = true := by
  have hf := g31_facts
  simp only [gFacts, Bool.and_eq_true] at hf
  have hf := hf.1
  simp only [gFactsV, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h32, hav, hsl, hm3, hb3s, hv22s, hi0, hop, hargs, hk4, hu29, hin, hu0, hu1,
    hrun⟩ := hf
  refine ⟨hl, ?_, h32, hav, hsl, hm3, ?_, ?_, hi0, hop, hargs, hk4, hu29, hin, hu0, hu1, hrun⟩
  · revert hres; cases checkG31 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb3s
    simp [blk3, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv22s
    simp [val, hv]

/-- The facts of `gFactsT` as hypotheses. -/
theorem factsT :
    1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk1 ∧
      blk1.values.size = 4 ∧ blk1.kind = .ARM64NZW ∧
      (kAt lc kt 1 blk1 4).get 4 = some 8 ∧ (kAt lc kt 1 blk1 4).get 5 = some 32 ∧
      uIn lc 1 = [] ∧ uL31 lc (uIn lc 1) blk1 4 = tbl ∧
      GenG1.okThen (stepTermLoc lc sT blk1)
        (fun r => GenG1.gotoIs r.1 3 && isW32 r.2.regs[5]?) = true := by
  have hf := g31_facts
  simp only [gFacts, Bool.and_eq_true] at hf
  have hf := hf.2
  simp only [gFactsT, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc] at hf
  obtain ⟨hm1, hb1s, hsz, hkind, hk4, hk5, hin1, hu, hrun⟩ := hf
  refine ⟨hm1, ?_, hsz, hkind, hk4, hk5, hin1, hu, hrun⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
  simp [blk1, hb]

/-! ## The activation -/

theorem g31Env (hc : checkG31 lc ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ := checkG31_spec hl hc
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ := checkG31_spec hl hc
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

/-! ## `v22`: `MOVD R4, R2` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 4 ∧ x = .int .w8 0x2a) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h4; exact Or.inl ⟨h4, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 3 0 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show BitVec.setWidth 8 (m0.x 4) = 0x2a
      decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g31Inv0 (h4 : (kAt lc kt 3 blk3 0).get 4 = some 8) :
    G3Inv E lc (kAt lc kt 3 blk3 0) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h4] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- `m0` keeps the table `tbl` from `b1`: `X5` and `X4` are zero-extended from 8 bits. -/
theorem uokl0 : UOKL m0 tbl := by
  intro e he
  simp only [tbl, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · show ∀ k : Nat, k < 31 → objX? 5 = some (BitVec.ofNat 5 k) →
      ExtOK (m0.x (BitVec.ofNat 5 k)) 8 false
    unfold ExtOK
    decide
  · show ∀ k : Nat, k < 31 → objX? 4 = some (BitVec.ofNat 5 k) →
      ExtOK (m0.x (BitVec.ofNat 5 k)) 8 false
    unfold ExtOK
    decide

/-- The per-value premises of `v22`, `MOVDreg`: none apply. -/
theorem pre22 {s : LocState} (hop : (val 22).op = .ARM64MOVDreg) : G14Pre lc s (val 22) := by
  have hne : ∀ o : Op, o ≠ .ARM64MOVDreg → (val 22).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G31 on `(*hexdumper).close`, values**: before `v22` (`MOVD R4, R2`, the first value of `b3`)
G29's table `uL` is empty, while G31's table is `uIn lc 3 = [(5, 8, false), (4, 8, false)]`, the
end of `b1`. From the state with the byte `0x2a` in `R4`, on a machine whose `X5` and `X4` are
zero-extended from 8 bits, `g31_value` runs `v22`: `runLoc`'s `R2` holds the 64-bit integer `0x2a`,
and the machine state, related to it before `v31` under an activation extending `E` that is again
a `G28Env`, has the whole `X2 = 0x2a`; it keeps the table, which gives the whole `X4 = 0x2a`
(`LocMatch` alone gives only its low 8 bits). -/
theorem genG31_value_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 22) = .ok s1 ∧
      s1.regs[2]? = some (.int .w64 0x2a) ∧ s1.regs[4]? = some (.int .w8 0x2a) ∧
      uL lc blk3 0 = [] ∧ uIn lc 3 = [(5, 8, false), (4, 8, false)] ∧
      uL31 lc (uIn lc 3) blk3 0 = [(5, 8, false), (4, 8, false)] ∧
      E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E1 s1 3 1 m1 ∧ UOKL m1 (uL31 lc (uIn lc 3) blk3 1) ∧
      m1.x 2 = 0x2a ∧ m1.x 4 = 0x2a := by
  obtain ⟨hl, hc, -, hav, hsl, hm3, hb, hv22, hi0, hop, -, hk4, hu29, hin, hu0, hu1, hrun⟩ :=
    factsV
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hr
  have hr2 := isW64_spec hr.1
  have hr4 := isW8_spec hr.2
  have hE := g31Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64MOVDreg → (val 22).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, hu1'⟩ := g31_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm3 hb hi0 hv22 (by rw [hop]; rfl) locMatch0 (g31Inv0 hk4) (by rw [hu0]; exact uokl0)
    (pre22 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  have hx2 : m1.x 2 = 0x2a := valRel_i64 hA ((hm1'.regs 2 _ hr2).1 2 rfl)
  have hext : ExtOK (m1.x 4) 8 false := by
    have h := hu1'
    rw [hu1] at h
    exact h (4, 8, false) (by simp [tbl1]) 4 (by decide) rfl
  have hlo : (m1.x 4).setWidth 8 = 0x2a := (hm1'.regs 4 _ hr4).1 4 rfl
  have hx4 : m1.x 4 = 0x2a := by
    simp only [ExtOK, Bool.false_eq_true, ↓reduceIte] at hext
    rw [hext, hlo]
    decide
  exact ⟨s1, E1, m1, hs1, hr2, hr4, hu29, hin, hu0, hx1, hE1, hp1, hm1', hu1', hx2, hx4⟩

/-! ## `b1`'s terminator: `CBZW R5` -/

theorem sT_regs {r : Nat} {x : Val} (h : sT.regs[r]? = some x) :
    (r = 4 ∧ x = .int .w8 0x2a) ∨ (r = 5 ∧ x = .int .w32 0x2a) ∨ x = .poison := by
  simp only [sT, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h4; exact Or.inl ⟨h4, h.symm⟩
    · split at h
      · rename_i h5; exact Or.inr (Or.inl ⟨h5, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatchT : LocMatch E sT 1 4 mT where
  regs := by
    intro r v hv
    rcases sT_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show BitVec.setWidth 8 (mT.x 4) = 0x2a
      decide
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show BitVec.setWidth 32 (mT.x 5) = 0x2a
      decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [sT] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, mT, E]; decide,
    by simp only [MState.word, readMem, mT, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g31InvT (h4 : (kAt lc kt 1 blk1 4).get 4 = some 8)
    (h5 : (kAt lc kt 1 blk1 4).get 5 = some 32) :
    G3Inv E lc (kAt lc kt 1 blk1 4) sT where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases sT_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h4] at hc; cases hc; rfl
    · rw [h5] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [sT] at h

/-- `mT` keeps the table `tbl` at `b1`'s end: `X5` and `X4` are zero-extended from 8 bits. -/
theorem uoklT : UOKL mT tbl := by
  intro e he
  simp only [tbl, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · show ∀ k : Nat, k < 31 → objX? 5 = some (BitVec.ofNat 5 k) →
      ExtOK (mT.x (BitVec.ofNat 5 k)) 8 false
    unfold ExtOK
    decide
  · show ∀ k : Nat, k < 31 → objX? 4 = some (BitVec.ofNat 5 k) →
      ExtOK (mT.x (BitVec.ofNat 5 k)) 8 false
    unfold ExtOK
    decide

/-- **G31 on `(*hexdumper).close`, terminators**: from the state at `b1`'s `NZW` (`CBZW R5`) with
the byte `0x2a` in `R4` and as a 32-bit integer in `R5`, on a machine whose `X5` and `X4` are
zero-extended from 8 bits (the table at `b1`'s end), `g31_term` runs to `b3`: the machine state is
related before `b3`'s first value with the registers at their classes, and keeps G31's start of
`b3`, `uIn lc 3 = [(5, 8, false), (4, 8, false)]`, so the whole `X5` is `0x2a` (`LocMatch` alone
gives only its low 32 bits). -/
theorem genG31_term_witness :
    ∃ s1 e m1, stepTermLoc lc sT blk1 = .ok (.goto e, s1) ∧ e.b = 3 ∧
      s1.regs[5]? = some (.int .w32 0x2a) ∧ uIn lc 3 = [(5, 8, false), (4, 8, false)] ∧
      PStar GenG2.H0 L ps.toList 0 mT m1 ∧ LocMatch E s1 3 0 m1 ∧ G3Inv E lc (kt.at 3) s1 ∧
      UOKL m1 (uIn lc 3) ∧ m1.x 5 = 0x2a := by
  obtain ⟨hl, hc, -, hav, hsl, -, -, -, -, -, -, -, -, hin, -⟩ := factsV
  obtain ⟨hm1, hb1, hsz, hkind, hk4, hk5, hin1, hu, hrun⟩ := factsT
  have hE := g31Env hc hl hav hsl
  obtain ⟨⟨n, s1⟩, hs1, hrun⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨hgo, hr5⟩ := hrun
  have hr5 := isW32_spec hr5
  obtain ⟨e, rfl, het⟩ := GenG1.gotoIs_spec hgo
  obtain ⟨m1, hp1, hlm1, hinv1, -, hu1⟩ := g31_term (H := GenG2.H0) hc hE hm1 hb1
    (by rw [hsz]; exact locMatchT) (by rw [hsz]; exact g31InvT hk4 hk5)
    (fun hz => by rw [hkind] at hz; rcases hz with h | h <;> cases h)
    (by rw [hsz, hu]; exact uoklT) hs1
  rw [het] at hlm1 hinv1 hu1
  have hext : ExtOK (m1.x 5) 8 false := by
    have h := hu1
    rw [hin] at h
    exact h (5, 8, false) (by simp [tbl]) 5 (by decide) rfl
  have hlo : (m1.x 5).setWidth 32 = 0x2a := (hlm1.regs 5 _ hr5).1 5 rfl
  have hlo8 : (m1.x 5).setWidth 8 = 0x2a := by
    rw [← BitVec.setWidth_setWidth_of_le (m1.x 5) (by decide : 8 ≤ 32), hlo]
    decide
  have hx5 : m1.x 5 = 0x2a := by
    simp only [ExtOK, Bool.false_eq_true, ↓reduceIte] at hext
    rw [hext, hlo8]
    decide
  exact ⟨s1, e, m1, hs1, het, hr5, hin, hp1, hlm1, hinv1, hu1, hx5⟩

end GoFV.Proof.Witness.GenG31
