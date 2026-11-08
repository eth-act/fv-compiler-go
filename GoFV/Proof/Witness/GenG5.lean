import GoFV.Proof.Gen.G5
import GoFV.Proof.Witness.GenG4

/-!
# Non-vacuity witness: slice G5 of the genssa validator on `g` of `test/stackobj`

`test/stackobj/main/g,1.ssa` and `test/stackobj/main/g,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`gSsa`, `gProg`):

```go
func g(s *StkObj) {
	gc()
	runtime.KeepAlive(s)
	gc()
}
```

`checkG4` rejects it (the marker `v11 = KeepAlive v2 v7`); `checkG5` accepts it with the PC table
`tab` and the class table `kt` (nothing known at the entry). By compiled evaluation
(`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g5_facts`), from the state after the
entry value `v5` (`s` in `R0`, here the integer 7), `stepLoc` runs the spill `v2` (`StoreReg` to
`s`'s parameter slot), the static call `v6` (`CALL main.gc(SB)`, no results), its memory `v7`
(`SelectN`) and the marker `v11` (`KeepAlive`, which reads the spilled `s` and keeps the memory);
the entry value `v1` (`InitMem`, no code) between `v2` and `v6` is not run. On GenG2's framed
activation layout (`SP = 0x7fff0000`, the slot at its frame operand with `autosize = 32`,
`extrasize = 8`, every symbol at `2^40`, the Progs at `0x10000 + 4·ID`, `ret = 0`) and GenG2's
callee contract (`H0` returns to `X30`; `env` returns no results and the memory), `g5_value` four
times gives a machine run of the Progs (`MOVD R0, s(FP)`; `CALL`, the hook) to a state related
before `v12`, with the registers at their classes (`genG5_value_witness`). `checkG5` also accepts
`pallocSum.start` (`GenG3`) with G3's tables; there `g5_term` runs the bit test `TBNZ [63]` to `b2`
(`genG5_term_witness`).
-/

namespace GoFV.Proof.Witness.GenG5

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/stackobj/main/g,1.ssa` (quick-v10). -/
def gSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "g" 1 0 0
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
type t6 INT64 8 8 0 comparable,named "int64" "int64"
type t5 ARRAY 64 8 0 comparable,named "HeapObj" "main.HeapObj" t6 8
type t4 PTR 8 8 8 hasptr,direct,comparable "*HeapObj" "*main.HeapObj" t5
type t3 STRUCT 8 8 8 hasptr,direct,comparable,named "StkObj" "main.StkObj" 1
field 0 "h" t4 0 0
type t2 PTR 8 8 8 hasptr,direct,comparable "*StkObj" "*main.StkObj" t3
type t1 FUNC 8 8 8 hasptr,direct "func(*StkObj)" "func(*main.StkObj)" 0 1 0
field 0 "s" t2 ? 0
aux a2 sym "main.g" "main.g" 1 - 0 - - - - 0
posbase p2 "./stackobj.go" 1 1 -1
aux a3 name "s" "s" PPARAM t2 0 1 used p2:53:8:0:0
aux a1 call "AuxCall{main.g}" a2 1 1 0 8 8 1 0
abiparam in 0 t2 a3 0 0
type t7 BOOL 1 1 0 comparable,named "bool" "bool"
type t8 INT8 1 1 0 comparable,named "int8" "int8"
type t9 INT16 2 2 0 comparable,named "int16" "int16"
type t10 INT32 4 4 0 comparable,named "int32" "int32"
type t11 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t12 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t13 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t14 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t15 INT 8 8 0 comparable,named "int" "int"
type t16 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t17 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t18 UINT 8 8 0 comparable,named "uint" "uint"
type t19 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t20 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t21 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t11
type t22 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t10
type t23 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t13
type t24 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t15
type t25 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t19
type t26 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t16
type t27 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t17
type t28 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t21
type t29 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t30 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t31 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t32 SSA ? ? ? - "mem" ""
type t33 SSA ? ? ? - "flags" ""
type t34 SSA ? ? ? - "void" ""
type t35 SSA 16 8 ? - "int128" ""
type t36 RESULTS ? ? ? - "mem" "" 1 t32
type t37 PTR 8 8 8 hasptr,direct,comparable "**StkObj" "**main.StkObj" t2
aux a5 sym "main.gc" "main.gc" 1 - 0 - - - - 0
aux a4 call "AuxCall{main.gc}" a5 1 0 0 8 0 0 0
aux a6 sym "type:*main.StkObj" "type:*main.StkObj" 0 SRODATA 56 - t2 - 08000000000000000800000000000000f46aa744280808160000000000000000000000000000000000000000000000000000000000000000 4
reloc 24 8 R_ADDR 0 "runtime.memequal64\xc2\xb7f" 0
reloc 32 8 R_ADDR 0 "runtime.gcbits.0100000000000000" 0
reloc 40 4 R_ADDROFF 0 "type:.namedata.*main.StkObj." 0
reloc 48 8 R_ADDR 0 "type:main.StkObj" 0
rtype 8 8 1151822580 22 "runtime.gcbits.0100000000000000" "type:main.StkObj"
type t38 INTER 16 8 16 hasptr,comparable,named,emptyiface "any" "interface {}"
aux a7 call "AuxCall{main.gc}" a5 1 0 0 8 0 0 0
slot s1 a3 t2 0 - 0
f b1 t1 a1 14 1
typs Bool=t7,Int8=t8,Int16=t9,Int32=t10,Int64=t6,UInt8=t11,UInt16=t12,UInt32=t13,UInt64=t14,Int=t15,Float32=t16,Float64=t17,UInt=t18,Uintptr=t19,String=t20,BytePtr=t21,Int32Ptr=t22,UInt32Ptr=t23,IntPtr=t24,UintptrPtr=t25,Float32Ptr=t26,Float64Ptr=t27,BytePtrPtr=t28,Complex64=t29,Complex128=t30,UnsafePtr=t31,Mem=t32,Flags=t33,Void=t34,Int128=t35,ResultMem=t36
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t37 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:0:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:0:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:0:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:0:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
dcllen 1
end
pass 1 "number lines"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t37 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t37 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 3 "early deadcode"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 4 "short circuit"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 5 "decompose user"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 7 "opt"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 8 "zero arg cse"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 9 "opt deadcode"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 2:54:57
dcllen 1
end
pass 10 "generic cse"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 11 "phiopt"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 12 "gcse deadcode"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 13 "nilcheckelim"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 14 "prove"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 15 "divisible"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 16 "divmod"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 17 "middle opt"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 18 "known bits"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 19 "early fuse"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p2:53:6:2:0 1 -
v v6 StaticLECall t36 0 a4 p2:54:4:1:0 1 v1
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticLECall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 20 "expand calls"
aux a8 nameoff "s+0" a3 0
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v9 IMake t38 0 - p2:55:20:0:0 1 v8,v5
v v10 IData t21 0 - p2:55:19:0:0 1 v9
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v10,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
v v4 SP t19 0 - p0:0:0:0:0 1 -
v v2 OffPtr t37 0 - p0:0:0:0:0 0 v4
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 21 "decompose builtin"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 2 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v9 IMake t38 0 - p2:55:20:0:0 0 v8,v5
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
v v4 SP t19 0 - p0:0:0:0:0 1 -
v v2 OffPtr t37 0 - p0:0:0:0:0 0 v4
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2
freev v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 22 "softfloat"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 2 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v9 IMake t38 0 - p2:55:20:0:0 0 v8,v5
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
v v4 SP t19 0 - p0:0:0:0:0 1 -
v v2 OffPtr t37 0 - p0:0:0:0:0 0 v4
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2
freev v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 23 "branchelim"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 2 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v8 Addr t21 0 a6 p0:0:0:0:0 1 v3
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v9 IMake t38 0 - p2:55:20:0:0 0 v8,v5
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
v v4 SP t19 0 - p0:0:0:0:0 1 -
v v2 OffPtr t37 0 - p0:0:0:0:0 0 v4
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2
freev v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 24 "late opt"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 25 "dead auto elim"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 26 "sccp"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 27 "generic deadcode"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 28 "late fuse"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 29 "check bce"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 30 "dse"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 31 "memcombine"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 32 "writebarrier"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 StaticCall t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 StaticCall t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 33 "lower"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 34 "addressing modes"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 35 "late lower"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 36 "pair"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 2:54:57
dcllen 1
end
pass 38 "lowered cse"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
dcllen 1
end
pass 39 "elim unread autos"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
dcllen 1
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
dcllen 1
end
pass 41 "lowered deadcode"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
dcllen 1
end
pass 42 "checkLower"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
dcllen 1
end
pass 43 "loop invariant"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
dcllen 1
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
dcllen 1
end
pass 45 "tighten"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
dcllen 1
end
pass 46 "late deadcode"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
dcllen 1
end
pass 47 "critical"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
dcllen 1
end
pass 48 "phi tighten"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
dcllen 1
end
pass 49 "likelyadjust"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
dcllen 1
end
pass 50 "layout"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
fstate laidout
dcllen 1
end
pass 51 "schedule"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
fstate scheduled,laidout
dcllen 1
end
pass 52 "late nilcheck"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
fstate scheduled,laidout
dcllen 1
end
pass 53 "flagalloc"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v5,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9,v8,v3,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
fstate scheduled,laidout
dcllen 1
end
pass 54 "regalloc"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v2 StoreReg t2 0 - p2:57:1:0:0 1 v5
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v2,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v8,v9,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
fstate scheduled,laidout
regalloc 6 v2:@a3/t2/0/-/0,v5:R0
dcllen 1
end
pass 55 "loop rotate"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v2 StoreReg t2 0 - p2:57:1:0:0 1 v5
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v2,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v8,v9,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
fstate scheduled,laidout
regalloc 6 v2:@a3/t2/0/-/0,v5:R0
dcllen 1
end
pass 56 "trim"
f b1 t1 a1 14 1
b b1 Ret p2:57:1:0:0 0 0 - v14 - -
v v5 ArgIntReg t2 0 a8 p2:57:1:0:0 1 -
v v2 StoreReg t2 0 - p2:57:1:0:0 1 v5
v v1 InitMem t32 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t36 0 a4 p2:54:4:1:0 1 v1
v v7 SelectN t32 0 - p2:54:4:0:0 1 v6
v v11 KeepAlive t32 0 - p2:55:19:1:0 1 v2,v7
v v12 ARM64CALLstatic t36 0 a7 p2:56:4:1:0 1 v11
v v13 SelectN t32 0 - p2:56:4:0:0 1 v12
v v14 MakeResult t36 0 - p2:57:1:1:0 1 v13
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v8,v9,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3,a8:4
cache linestarts 2:54:57
fstate scheduled,laidout
regalloc 6 v2:@a3/t2/0/-/0,v5:R0
dcllen 1
end
frontend
end
ptrcache t3,t5,t6,t9,t10,t11,t13,t15,t16,t17,t19,t20,t21,t28
typelink t32=t36
typeorder t8,t11,t9,t12,t10,t13,t6,t14,t15,t18,t19,t29,t30,t16,t17,t7,t21,t22,t23,t24,t25,t26,t27,t28,t37,t4,t2,t1,t5,t3,t38,t20,t31,t32,t34,t33,t35,t36
eof
"#

/-- `test/stackobj/main/g,1.prog` (quick-v10). -/
def gProg : String := r#"gofv-prog 3
pkg "main"
func "g" 1
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
type t1 8 8 8 1 01 "*StkObj"
name n1 "s" PPARAM t1 1 "main.s" 0 a3
in n1 0 used
out n1 0 used
stack 0 0 8
end
genin
posbase p2 "./stackobj.go" 1 1 -1 1 "./stackobj.go" "./stackobj.go" 1 1
sym y1 "main.g" 1
curfn p2:53:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 53 200080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "main.g.arginfo1" 0
sym y5 "main.g.argliveinfo" 0
sym y6 "main.s" 0
sym y7 "main.gc" 1
sym y8 "type:*main.StkObj" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:53:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:53:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:53:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:53:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:53:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:53:6:2:0
p 6 6 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/PARAM/0/0/y6/- 0 0 p2:57:1:2:0
p 7 7 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:57:1:2:0
p 8 8 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p2:54:4:1:0
p 9 9 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p2:54:4:1:0
p 10 10 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:56:4:1:0
p 11 11 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p2:56:4:1:0
p 12 12 0 0 0 - RET 0 _ 0 - _ 0 0 p2:57:1:0:0
p 13 13 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 53 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 1
reloc 0 0 R_USEIFACE 0 y8
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:1:6:50,1:6:-1:-30000:9108
dbgregout -
dbgpc 1:6:10
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p2:53:6:0:0
p 14 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:53:6:0:0
p 15 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:53:6:0:0
p 16 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:53:6:0:0
p 17 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@26 0 0 p2:53:6:0:0
p 18 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:53:6:0:0
p 19 12 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p2:53:6:0:1
p 20 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:53:6:0:0
p 21 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:53:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:53:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:53:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:53:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p2:53:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:53:6:2:0
p 6 24 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/0/y6/- 0 0 p2:57:1:2:0
p 7 28 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:57:1:2:0
p 8 28 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p2:54:4:1:0
p 9 28 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y7/- 0 0 p2:54:4:1:0
p 10 32 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:56:4:1:0
p 11 32 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y7/- 0 0 p2:56:4:1:0
p 12 36 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:57:1:0:0
p 22 40 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:57:1:0:0
p 23 44 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:57:1:0:0
p 24 48 -16 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:57:1:0:0
p 25 48 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:53:6:0:0
p 26 48 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:53:6:0:0
p 27 48 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p2:53:6:0:0
p 28 52 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:53:6:0:0
p 29 56 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y9/- 0 0 p2:53:6:0:0
p 30 60 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:53:6:0:0
p 31 60 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:53:6:0:0
p 32 64 16 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@14 0 0 p2:53:6:0:0
fn y1 8 8 0 0 53 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 80 0 900b40f9ff6330eb49010054fe0f1ff8fd831ff8fd2300d1e00f00f90000009400000094fd835ff8fe0741f8c0035fd6e00700f9e3031eaa00000094e00740f9f0ffff17000000000000000000000000 4
reloc 0 0 R_USEIFACE 0 y8
reloc 28 4 R_CALLARM64 0 y7
reloc 32 4 R_CALLARM64 0 y7
reloc 56 4 R_CALLARM64 0 y9
pcln y14 y15 y16 y17 y10,y11,y12,y13 y2,y3,_,_,_,y4,y5
usedfiles 1
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y10 SRODATA 11 1 28000 0001010202090103020500 0
data y11 SRODATA 9 1 28000 000702010204030800 0
data y12 SRODATA 0 1 28000 - 0
data y13 SRODATA 7 1 28000 00060401030d00 0
data y14 SRODATA 7 1 28000 020420071f0900 0
data y15 SRODATA 3 1 28000 041400 0
data y16 SRODATA 13 1 28000 6c060801050104010203070800 0
data y17 SRODATA 3 1 28000 001400 0
end
dwarf
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
sym y21 "" 0
sym y22 "go:info.*main.StkObj" 0
dwfn y18 y19 y20 - y21 "main.g" 1:53 1 0 1 6
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwname n1 1 1 0 0 0 0 0 0 - - "*main.StkObj" 0 0 1 p2:53:8:0:0
var 0 0 "s" 5 1 0 0 0 8 y22 "./stackobj.go" 53 8 0 0 0 0 v0
scope 0 0 - 0
data y18 SDWARFFCN 32 0 0 036d61696e2e67000050019c0200000035012d73000035000000000000000000 4
reloc 0 0 R_USETYPE 0 y8
reloc 8 1 R_DWTXTADDR_U1 0 y1
reloc 23 4 R_DWARFSECREF 0 y22
reloc 27 4 R_DWARFSECREF 0 y19
data y19 SDWARFLOC 14 0 0 0100040020015004205002910800 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y20 SDWARFRANGE 0 0 0 - 0
data y21 SDWARFLINES 30 0 0 00090200000000000000000402032f140a87068b06343938830220000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded `g` (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG5` gives (block `b1`: the index of each value's first Prog and of the
terminator's; `v11` at 5 emits nothing, so `v12` starts at the same index 10). -/
def tab : PcTab := [(1, [5, 5, 7, 7, 10, 10, 10, 12, 12, 12])]

/-- The class table `checkG5` gives: nothing known at the entry `b1`. -/
def kt : KTab := [(1, KMap.bot)]

/-- Block `b1`: `v5 = ArgIntReg` (`R0`), `v2 = StoreReg v5`, `v1 = InitMem`, `v6 = CALLstatic v1`,
`v7 = SelectN [0] v6`, `v11 = KeepAlive v2 v7`, `v12 = CALLstatic v11`, `v13 = SelectN [0] v12`,
`v14 = MakeResult v13`; `Ret`. -/
def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: GenG2's (the Prog with ID `n` at `0x10000 + 4n`, a 32-byte frame with 8 bytes of
extra space, every symbol at `symA`). -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 32 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the home
slots at their frame operands and the PC table of `checkG5`. -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := GenG2.sp0,
    slot := fun k => if k ∈ homeSlots lc then (g.slotOp k).map (fun p => frameOff L p.1 p.2) else none,
    g := 0x9000, lr := 0, fp := 0, framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The machine before `v2`: `X0 = x`, the activation's `g` and `FP`, the PC of `v2`. -/
def m0 (x : BitVec 64) : MState :=
  { x := fun k => if k = 0 then x else if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 1, mem := fun _ => 0 }

/-- The static call `v` has no results. -/
def noOuts (v : Value) : Bool :=
  match callOf? lc.ctx.tabs v.aux with
  | some (_, _, cabi) =>
    match callRegs cabi with
    | .ok (_, outs) => outs.isEmpty
    | .error _ => true
  | none => true

/-- The home slots lie above the saved `LR` and below `2^64`. -/
def slotsFit : Bool :=
  (homeSlots lc).all fun k =>
    match g.slotOp k with
    | some (nc, off) => decide (8 ≤ frameOff L nc off) &&
        decide (GenG2.sp0.toNat + (frameOff L nc off).toNat + 8 ≤ 2 ^ 64)
    | none => true

/-- What compiled evaluation checks on `g`: `checkG5` accepts it with `tab` and `kt` and `checkG4`
does not; `b1` holds `v2`, `v6`, `v7`, `v11` at 1, 3, 4, 5 with their ops; `v6` has no results;
the slots fit; `R0` holds a 64-bit value after `v5`, and the class map is the same before and after
`v1`; and `stepLoc` runs `v2`, `v6` (to the memory `mem0`), `v7`, `v11`. -/
def gFacts (x : BitVec 64) : Bool :=
  (checkG5 lc ps bs g).toOption == some (tab, kt) && (checkG4 lc ps bs g).toOption.isNone &&
    lc.ctx.f.blocks.toList.contains 1 &&
    (lc.ctx.f.block? 1).isSome && (lc.ctx.f.value? 2).isSome && (lc.ctx.f.value? 6).isSome &&
    (lc.ctx.f.value? 7).isSome && (lc.ctx.f.value? 11).isSome &&
    blk1.values[1]? == some 2 && blk1.values[3]? == some 6 && blk1.values[4]? == some 7 &&
    blk1.values[5]? == some 11 &&
    (val 2).op == .StoreReg && (val 6).op == .ARM64CALLstatic && (val 7).op == .SelectN &&
    (val 11).op == .KeepAlive && noOuts (val 6) && slotsFit &&
    (kAt lc kt 1 blk1 1).get 0 == some 64 && kAt lc kt 1 blk1 3 == kAt lc kt 1 blk1 2 &&
    GenG1.okThen (stepLoc GenG2.env lc (GenG2.s0 x) (val 2)) fun s1 =>
      GenG1.okThen (stepLoc GenG2.env lc s1 (val 6)) fun s2 => GenG2.memIs0 s2.mem &&
        GenG1.okThen (stepLoc GenG2.env lc s2 (val 7)) fun s3 =>
          GenG1.okThen (stepLoc GenG2.env lc s3 (val 11)) fun _ => true

/-- `checkG5` accepts `pallocSum.start` (`GenG3`) with G3's tables. -/
def startG5 : Bool :=
  (checkG5 GenG3.lc GenG3.ps GenG3.bs GenG3.g).toOption == some (GenG3.tab, GenG3.kt)

theorem g5_facts : (gFacts 7 && startG5) = true := by
  native_decide

theorem g_facts : gFacts 7 = true := by
  have h := g5_facts
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem g5Env (hc : checkG5 lc ps bs g = .ok (tab, kt)) : G2Env lc g L ps 0 tab E where
  lcEq := rfl
  link := rfl
  pcOf := rfl
  retOut := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG5_spec hc
    intro p hp
    exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
  addr := GenG2.addrAgree
  glob := fun _ _ _ _ => rfl
  syms := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG5_spec hc
    intro y
    have hs : L.sym y = GenG2.symA := rfl
    rw [hs]
    refine ⟨by decide, fun p hp => ?_⟩
    exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
  calls := fun h => by cases h
  slot := fun k hk nc off hs => by simp [E, hk, hs]
  extra := by decide
  frame := by
    refine ⟨by decide, by decide, fun k off hk => ?_⟩
    have hf := g_facts
    simp only [gFacts, Bool.and_eq_true] at hf
    have hfit := hf.1.1.1.2
    simp only [E] at hk
    split at hk
    · rename_i hmem
      obtain ⟨⟨nc, o⟩, hso, rfl⟩ := Option.map_eq_some_iff.1 hk
      have := List.all_eq_true.1 hfit k hmem
      simp only [hso, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this
    · cases hk

theorem locMatch0 (x : BitVec 64) : LocMatch E (GenG2.s0 x) 1 1 (m0 x) where
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
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g5Inv0 (x : BitVec 64) {K : KMap} (h0 : K.get 0 = some 64) :
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

/-- The callee contract of a callee that returns at once with the memory `mem0` and no
results. -/
theorem callOK0 {E' : MatchEnv} (hA : AddrAgree E'.ι) (hnil : E'.ι .nil = some 0)
    {s s' : LocState} {v : Value} {m : MState} (hmem : GenG2.memIs0 s'.mem = true)
    (hno : noOuts v = true) : CallOK GenG2.H0 E' g L lc s s' v m := by
  intro _ name abi cabi ins outs y args mm m₁ hc hcr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hout : outs = [] := by
    simp only [noOuts, hc, hcr, List.isEmpty_iff] at hno
    exact hno
  have hm' : s'.mem = .mem GenG2.mem0 := by
    unfold GenG2.memIs0 at hmem
    split at hmem
    · rename_i mm' he
      rw [he, of_decide_eq_true hmem]
    · cases hmem
  subst hout
  exact ⟨E'.ι, { m₁ with pc := m₁.x 30 }, GenG2.mem0, rfl, fun _ _ h => h, hA, rfl, rfl, rfl, rfl,
    fun _ _ => rfl, hm', GenG2.memInj0 hnil _, GenG2.keys0, GenG2.sep0, fun r hr => by cases hr⟩

/-- The per-value premises of a value that is no compare, load, pair load or subtraction. -/
theorem g5Pre_of {v : Value} (h1 : v.op ≠ .ARM64CMP) (h2 : v.op ≠ .ARM64CMPconst)
    (h3 : loadOp? v.op = none) (h4 : v.op ≠ .ARM64LDP) (h5 : v.op ≠ .ARM64SUB) (s : LocState) :
    G4Pre lc s v :=
  ⟨⟨fun h => by rcases h with h | h <;> contradiction,
    (fun _ _ _ hl => by rw [h3] at hl; cases hl), fun h => absurd h h5⟩, fun h => absurd h h4⟩

/-- **G5 on `g`**: from the state after `v5` (`R0 = 7`), the spill `v2`, the call `v6`, its memory
`v7` and the marker `v11` (`KeepAlive`) are matched by a machine run of the Progs to a state related
before `v12`, with the registers at their classes, under an activation that extends `E`. -/
theorem genG5_value_witness :
    ∃ s1 s2 s3 s4 E' m4, stepLoc GenG2.env lc (GenG2.s0 7) (val 2) = .ok s1 ∧
      stepLoc GenG2.env lc s1 (val 6) = .ok s2 ∧ stepLoc GenG2.env lc s2 (val 7) = .ok s3 ∧
      stepLoc GenG2.env lc s3 (val 11) = .ok s4 ∧ E.Extends E' ∧ G2Env lc g L ps 0 tab E' ∧
      PStar GenG2.H0 L ps.toList 0 (m0 7) m4 ∧ LocMatch E' s4 1 6 m4 ∧
      G3Inv E' lc (kAt lc kt 1 blk1 6) s4 := by
  have hf := g_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, -⟩, hmem⟩, hbs⟩, hv2s⟩, hv6s⟩, hv7s⟩, hv11s⟩, hi1⟩, hi3⟩,
    hi4⟩, hi5⟩, hop2⟩, hop6⟩, hop7⟩, hop11⟩, hno⟩, -⟩, hk0⟩, hk3⟩, hrun⟩ := hf
  have hc : checkG5 lc ps bs g = .ok (tab, kt) := by
    revert hck; cases checkG5 lc ps bs g <;> simp [Except.toOption]
  have hb : lc.ctx.f.block? 1 = some blk1 := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk1, hb]
  have hval : ∀ n, (lc.ctx.f.value? n).isSome = true → lc.ctx.f.value? n = some (val n) := by
    intro n h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    simp [val, hv]
  have hE := g5Env hc
  obtain ⟨s1, hs1, hrun⟩ := GenG1.okThen_spec hrun
  obtain ⟨s2, hs2, hrun⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨hm2, hrun⟩ := hrun
  obtain ⟨s3, hs3, hrun⟩ := GenG1.okThen_spec hrun
  obtain ⟨s4, hs4, -⟩ := GenG1.okThen_spec hrun
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, hinv1⟩ := g5_value (H := GenG2.H0) hc hE hmem hb hi1
    (hval 2 hv2s) (by rw [hop2]; rfl) (locMatch0 7) (g5Inv0 7 hk0)
    (g5Pre_of (by rw [hop2]; decide) (by rw [hop2]; decide)
      (by rw [hop2]; simp [loadOp?, narrowLoad?]) (by rw [hop2]; decide) (by rw [hop2]; decide) _)
    (GenG2.callOK_ne (by rw [hop2]; decide)) hs1
  have hidx : ((tab.lookup 1).getD []).getD 3 0 = ((tab.lookup 1).getD []).getD 2 0 := by decide
  have hm1' : LocMatch E1 s1 1 3 m1 := by
    refine locMatch_pc hm1 ?_
    rw [hm1.pc, hx1.1]
    show pcOfTab GenG2.text ps.toList tab 1 3 = pcOfTab GenG2.text ps.toList tab 1 (1 + 1)
    unfold pcOfTab
    rw [hidx]
  have hinv1' : G3Inv E1 lc (kAt lc kt 1 blk1 3) s1 := by rw [hk3]; exact hinv1
  have hA1 := hE1.addr
  obtain ⟨E2, m2, hx2, hE2, hp2, hm2', hinv2⟩ := g5_value (H := GenG2.H0) hc hE1 hmem hb hi3
    (hval 6 hv6s) (by rw [hop6]; rfl) hm1' hinv1'
    (g5Pre_of (by rw [hop6]; decide) (by rw [hop6]; decide)
      (by rw [hop6]; simp [loadOp?, narrowLoad?]) (by rw [hop6]; decide) (by rw [hop6]; decide) _)
    (callOK0 hA1 (hx1.2 _ _ rfl) hm2 hno) hs2
  obtain ⟨E3, m3, hx3, hE3, hp3, hm3, hinv3⟩ := g5_value (H := GenG2.H0) hc hE2 hmem hb hi4
    (hval 7 hv7s) (by rw [hop7]; rfl) hm2' hinv2
    (g5Pre_of (by rw [hop7]; decide) (by rw [hop7]; decide)
      (by rw [hop7]; simp [loadOp?, narrowLoad?]) (by rw [hop7]; decide) (by rw [hop7]; decide) _)
    (GenG2.callOK_ne (by rw [hop7]; decide)) hs3
  obtain ⟨E4, m4, hx4, hE4, hp4, hm4, hinv4⟩ := g5_value (H := GenG2.H0) hc hE3 hmem hb hi5
    (hval 11 hv11s) (by rw [hop11]; rfl) hm3 hinv3
    (g5Pre_of (by rw [hop11]; decide) (by rw [hop11]; decide)
      (by rw [hop11]; simp [loadOp?, narrowLoad?]) (by rw [hop11]; decide)
      (by rw [hop11]; decide) _)
    (GenG2.callOK_ne (by rw [hop11]; decide)) hs4
  exact ⟨s1, s2, s3, s4, E4, m4, hs1, hs2, hs3, hs4,
    MatchEnv.Extends.trans (MatchEnv.Extends.trans (MatchEnv.Extends.trans hx1 hx2) hx3) hx4,
    hE4, ((hp1.trans hp2).trans hp3).trans hp4, hm4, hinv4⟩

/-- **G5 on `pallocSum.start`**: `g5_term` on the bit test `TBNZ [63]` (bit 63 of `x = 7` clear)
gives a machine run to a state related before the first value of `b2`, with the registers at its
classes. -/
theorem genG5_term_witness :
    ∃ s1 e m1, stepTermLoc GenG3.lc (GenG2.s0 7) GenG3.blk1 = .ok (.goto e, s1) ∧ e.b = 2 ∧
      PStar GenG2.H0 GenG3.L GenG3.ps.toList 0 (GenG3.m0 7) m1 ∧ LocMatch GenG3.E s1 2 0 m1 ∧
      G3Inv GenG3.E GenG3.lc (GenG3.kt.at 2) s1 := by
  have h := g5_facts
  simp only [Bool.and_eq_true] at h
  have hc5 : checkG5 GenG3.lc GenG3.ps GenG3.bs GenG3.g = .ok (GenG3.tab, GenG3.kt) := by
    have h2 := h.2
    simp only [startG5, beq_iff_eq] at h2
    revert h2; cases checkG5 GenG3.lc GenG3.ps GenG3.bs GenG3.g <;> simp [Except.toOption]
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
  obtain ⟨m1, hp1, hlm1, hinv1, -⟩ := g5_term (H := GenG2.H0) hc5 hE hm1 hb1
    (GenG3.locMatch0 7) (GenG3.g3Inv0 7 (by rw [hsz]; exact hk0))
    (fun hz => by rw [hkind] at hz; rcases hz with h | h <;> cases h) hs1
  exact ⟨s1, e, m1, hs1, het, hp1, het ▸ hlm1, het ▸ hinv1⟩

end GoFV.Proof.Witness.GenG5
