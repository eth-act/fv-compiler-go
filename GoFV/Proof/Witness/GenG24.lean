import GoFV.Proof.Gen.G24
import GoFV.Proof.Witness.GenG23

/-!
# Non-vacuity witness: slice G24 of the genssa validator on `SChan.Recv` of `test/closedchan`

`test/closedchan/main/(*SChan).Recv,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`): the wrapper the
compiler generates for the value method

```go
func (c SChan) Recv() int {
	select {
	case x := <-c:
		return x
	}
}
```

`checkG23` rejects it (`v2: SP after the entry values`: `SP` heads the receiving block `b5`, after
the entry block `b1`'s nil test of the receiver); `checkG24` accepts it with the PC table `tab` and
the class table `kt`. Block `b5`: `v2 = SP` (no code), the load of `*c`, the address of the frame
variable `.autotmp_6` off `v2` and the call of `runtime.chanrecv2`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g24_facts`),
`stepLoc` runs `v2` from a state with `c = 5` in `R0`: the Go register `SP` then holds `SP`'s
value at its `uintptr` shape (`2^62`). On GenG6's framed layout with `.autotmp_6` (aux 7, operand
`-8`, `NAME_AUTO`) at `SP + 16` under the injection (`G10Env`) and `X0 = 5`, `g24_value` relates
the state after `v2` to a machine state at the same PC: `SP` runs no code
(`genG24_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG24

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/closedchan/main/(*SChan).Recv,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "(*SChan).Recv" 1 0 0
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
type t3 CHAN 8 8 8 hasptr,direct,comparable,named "SChan" "main.SChan"
type t2 PTR 8 8 8 hasptr,direct,comparable "*SChan" "*main.SChan" t3
type t4 INT 8 8 0 comparable,named "int" "int"
type t1 FUNC 8 8 8 hasptr,direct "method(*SChan) func() int" "method(*main.SChan) func() int" 1 0 1
field 0 "c" t2 ? 0
field 1 "" t4 ? 0
aux a2 sym "main.(*SChan).Recv" "main.(*SChan).Recv" 1 - 0 - - - - 0
posbase p2 "./closedchan.go" 1 1 -1
aux a3 name "c" "c" PPARAM t2 0 1 used p2:102:7:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t4 0 1 - p2:102:23:0:0
aux a1 call "AuxCall{main.(*SChan).Recv}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t4 a4 0 -1
type t5 BOOL 1 1 0 comparable,named "bool" "bool"
type t6 INT8 1 1 0 comparable,named "int8" "int8"
type t7 INT16 2 2 0 comparable,named "int16" "int16"
type t8 INT32 4 4 0 comparable,named "int32" "int32"
type t9 INT64 8 8 0 comparable,named "int64" "int64"
type t10 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t11 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t12 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t13 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t14 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t15 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t16 UINT 8 8 0 comparable,named "uint" "uint"
type t17 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t18 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t8
type t21 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t12
type t22 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t4
type t23 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t17
type t24 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t14
type t25 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t15
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
type t35 PTR 8 8 8 hasptr,direct,comparable "**SChan" "**main.SChan" t2
aux a5 sym "type:string" "type:string" 0 - 0 - t18 - - 0
rtype 16 8 -125357384 24 "runtime.gcbits.0100000000000000" ""
type t36 PTR 8 8 8 hasptr,direct,comparable "*string" "*string" t18
aux a6 sym "main..stmp_24" "main..stmp_24" 0 SRODATA 16 local,static,contentaddressable - - 00000000000000000400000000000000 1
reloc 0 8 R_ADDR 0 "go:string.\"recv\"" 0
type t37 CHAN 8 8 8 hasptr,direct,comparable "<-chan int" "<-chan int"
posbase p20 "./closedchan.go" 1 1 15
aux a7 name ".autotmp_6" ".autotmp_6" PAUTO t4 0 3 addrtaken,used,autotmp p20:104:2:0:0
type t38 RESULTS ? ? ? - "bool,mem" "" 2 t5,t30
aux a9 sym "runtime.chanrecv2" "runtime.chanrecv2" 1 - 0 - - - - 0
aux a8 call "AuxCall{runtime.chanrecv2}" a9 1 2 1 8 16 2 1
abiparam in 0 t37 - 0 0
abiparam in 1 t22 - 1 8
abiparam out 0 t5 - 0 -1
aux a11 sym "runtime.panicwrap" "runtime.panicwrap" 1 - 0 - - - - 0
aux a10 call "AuxCall{runtime.panicwrap}" a11 1 0 0 8 0 0 0
type t39 INTER 16 8 16 hasptr,comparable,named,emptyiface "any" "interface {}"
aux a13 sym "runtime.gopanic" "runtime.gopanic" 1 - 0 - - - - 0
type t40 INTER 16 8 16 hasptr,comparable,emptyiface "interface {}" "interface {}"
aux a12 call "AuxCall{runtime.gopanic}" a13 1 1 0 8 16 2 0
abiparam in 0 t40 - 0,1 0
type t41 RESULTS ? ? ? - "int,mem" "" 2 t4,t30
slot s1 a3 t2 0 - 0
aux a14 name "c" "c" PAUTO t3 0 1 used p20:102:7:0:0
slot s2 a14 t3 0 - 0
aux a15 name "x" "x" PAUTO t4 0 1 used p20:104:7:0:0
slot s3 a15 t4 0 - 0
aux a16 name "~r0" "~r0" PAUTO t4 0 1 - p20:102:23:0:0
slot s4 a16 t4 0 - 0
f b1 t1 a1 33 5
typs Bool=t5,Int8=t6,Int16=t7,Int32=t8,Int64=t9,UInt8=t10,UInt16=t11,UInt32=t12,UInt64=t13,Int=t4,Float32=t14,Float64=t15,UInt=t16,Uintptr=t17,String=t18,BytePtr=t19,Int32Ptr=t20,UInt32Ptr=t21,IntPtr=t22,UintptrPtr=t23,Float32Ptr=t24,Float64Ptr=t25,BytePtrPtr=t26,Complex64=t27,Complex128=t28,UnsafePtr=t29,Mem=t30,Flags=t31,Void=t32,Int128=t33,ResultMem=t34
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 4 -
v v3 SB t17 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t22 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 Const64 t4 0 - p0:0:0:0:0 0 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:0:0 1 v6,v8
v v25 Addr t19 0 a5 p0:0:0:0:0 1 v3
v v26 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 Plain p1:1:0:1:0 0 0 - - b5:0 b1:1
v v13 Copy t2 0 - p1:1:0:2:0 1 v6
v v14 Copy t30 0 - p1:1:0:2:0 5 v1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v13,v14
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v14
v v17 InlMark t32 15 - p1:1:0:1:0 0 v14
v v18 Copy t37 0 - p20:104:9:2:0 1 v16
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 1 v2,v14
v v20 StaticLECall t38 16 a8 p20:104:9:0:0 2 v18,v19,v14
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v22 SelectN t5 0 - p20:104:9:0:0 0 v20
v v23 LocalAddr t22 0 a7 p20:104:2:2:0 1 v2,v21
v v24 Load t4 0 - p20:104:2:0:0 1 v23,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v10 Copy t30 0 - p1:1:0:2:0 1 v1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v10
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 Exit p20:107:8:0:0 0 0 - v30 - -
v v27 IMake t39 0 - p20:107:8:0:0 1 v25,v26
v v28 Unknown t30 0 - p20:107:7:2:0 1 -
v v29 StaticLECall t34 16 a12 p20:107:7:0:0 1 v27,v28
v v30 SelectN t30 0 - p20:107:7:0:0 1 v29
b b5 Ret p1:1:0:1:0 0 0 - v33 - b2:0
v v31 Copy t4 0 - p1:1:0:2:0 1 v24
v v32 Copy t30 0 - p1:1:0:2:0 1 v21
v v33 MakeResult t41 0 - p1:1:0:0:0 1 v31,v32
names s1,s2,s3,s4
named s1 v6,v13
named s2 v16
named s3 v24
named s4 v24,v31
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts 0=v7,3344556677=v8
freev -
freeb -
dcllen 7
end
pass 1 "number lines"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 4 -
v v3 SB t17 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t22 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v7 Const64 t4 0 - p0:0:0:0:0 0 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:1:0 1 v6,v8
v v25 Addr t19 0 a5 p0:0:0:0:0 1 v3
v v26 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 Plain p1:1:0:1:0 0 0 - - b5:0 b1:1
v v13 Copy t2 0 - p1:1:0:2:0 1 v6
v v14 Copy t30 0 - p1:1:0:2:0 5 v1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v13,v14
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v14
v v17 InlMark t32 15 - p1:1:0:0:0 0 v14
v v18 Copy t37 0 - p20:104:9:2:0 1 v16
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 1 v2,v14
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 2 v18,v19,v14
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v22 SelectN t5 0 - p20:104:9:0:0 0 v20
v v23 LocalAddr t22 0 a7 p20:104:2:2:0 1 v2,v21
v v24 Load t4 0 - p20:104:2:0:0 1 v23,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v10 Copy t30 0 - p1:1:0:2:0 1 v1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v10
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 Exit p20:107:8:0:0 0 0 - v30 - -
v v27 IMake t39 0 - p20:107:8:0:0 1 v25,v26
v v28 Unknown t30 0 - p20:107:7:2:0 1 -
v v29 StaticLECall t34 16 a12 p20:107:7:0:0 1 v27,v28
v v30 SelectN t30 0 - p20:107:7:0:0 1 v29
b b5 Ret p1:1:0:1:0 0 0 - v33 - b2:0
v v31 Copy t4 0 - p1:1:0:2:0 1 v24
v v32 Copy t30 0 - p1:1:0:2:0 1 v21
v v33 MakeResult t41 0 - p1:1:0:0:0 1 v31,v32
names s1,s2,s3,s4
named s1 v6,v13
named s2 v16
named s3 v24
named s4 v24,v31
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts 0=v7,3344556677=v8
freev -
freeb -
cache postorder b3,b5,b2,b1
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v2 SP t17 0 - p0:0:0:0:0 4 -
v v3 SB t17 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t22 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p1:1:0:2:0 3 -
v v7 Const64 t4 0 - p0:0:0:0:0 0 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:1:0 1 v6,v8
v v25 Addr t19 0 a5 p0:0:0:0:0 1 v3
v v26 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 Plain p1:1:0:1:0 0 0 - - b5:0 b1:1
v v13 Copy t2 0 - p1:1:0:2:0 0 v6
v v14 Copy t30 0 - p1:1:0:2:0 0 v1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 2 v15,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v18 Copy t37 0 - p20:104:9:2:0 0 v16
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 1 v2,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 2 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 4 v20
v v22 SelectN t5 0 - p20:104:9:0:0 0 v20
v v23 LocalAddr t22 0 a7 p20:104:2:2:0 1 v2,v21
v v24 Load t4 0 - p20:104:2:0:0 2 v23,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v10 Copy t30 0 - p1:1:0:2:0 0 v1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b4 Exit p20:107:8:0:0 0 0 - v30 - -
v v27 IMake t39 0 - p20:107:8:0:0 1 v25,v26
v v28 Unknown t30 0 - p20:107:7:2:0 1 -
v v29 StaticLECall t34 16 a12 p20:107:7:0:0 1 v27,v28
v v30 SelectN t30 0 - p20:107:7:0:0 1 v29
b b5 Ret p1:1:0:1:0 0 0 - v33 - b2:0
v v31 Copy t4 0 - p1:1:0:2:0 0 v24
v v32 Copy t30 0 - p1:1:0:2:0 0 v21
v v33 MakeResult t41 0 - p1:1:0:0:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6,v6
named s2 v16
named s3 v24
named s4 v24,v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts 0=v7,3344556677=v8
freev -
freeb -
cache postorder b3,b5,b2,b1
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 3 "early deadcode"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:1:0 1 v6,v8
b b2 Plain p1:1:0:1:0 0 0 - - b5:0 b1:1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 1 v2,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v23 LocalAddr t22 0 a7 p20:104:2:2:0 1 v2,v21
v v24 Load t4 0 - p20:104:2:0:0 1 v23,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b2:0
v v33 MakeResult t41 0 - p1:1:0:0:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts 3344556677=v8
freev v32,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b4
cache postorder b3,b5,b2,b1
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 4 "short circuit"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b5:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:1:0 1 v6,v8
b b2 BlockInvalid p1:1:0:1:0 0 0 - - - -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 1 v2,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v23 LocalAddr t22 0 a7 p20:104:2:2:0 1 v2,v21
v v24 Load t4 0 - p20:104:2:0:0 1 v23,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts 3344556677=v8
freev v32,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 5 "decompose user"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b5:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:1:0 1 v6,v8
b b2 BlockInvalid p1:1:0:1:0 0 0 - - - -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 1 v2,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v23 LocalAddr t22 0 a7 p20:104:2:2:0 1 v2,v21
v v24 Load t4 0 - p20:104:2:0:0 1 v23,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts 3344556677=v8
freev v32,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v9 b3:0,b5:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 ConstNil t2 0 - p0:0:0:0:0 1 -
v v9 EqPtr t5 0 - p1:1:0:1:0 1 v6,v8
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:0
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:1
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 1 v2,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v23 LocalAddr t22 0 a7 p20:104:2:2:0 1 v2,v21
v v24 Load t4 0 - p20:104:2:0:0 1 v23,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts 3344556677=v8
freev v32,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 7 "opt"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 1 v2,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v23 LocalAddr t22 0 a7 p20:104:2:2:0 1 v2,v21
v v24 Load t4 0 - p20:104:2:0:0 1 v23,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 8 "zero arg cse"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 1 v2,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v23 LocalAddr t22 0 a7 p20:104:2:2:0 1 v2,v21
v v24 Load t4 0 - p20:104:2:0:0 1 v23,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 9 "opt deadcode"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 1 v2,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v23 LocalAddr t22 0 a7 p20:104:2:2:0 1 v2,v21
v v24 Load t4 0 - p20:104:2:0:0 1 v23,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 10 "generic cse"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v23 LocalAddr t22 0 a7 p20:104:2:2:0 0 v2,v21
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 11 "phiopt"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v23 LocalAddr t22 0 a7 p20:104:2:2:0 0 v2,v21
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 12 "gcse deadcode"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v15 NilCheck t2 0 - p1:1:0:0:0 1 v6,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v23,v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 13 "nilcheckelim"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v15 Copy t2 0 - p1:1:0:0:0 1 v6
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v23,v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 14 "prove"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v15 Copy t2 0 - p1:1:0:0:0 1 v6
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v15,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v23,v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 15 "divisible"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v15,v23,v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 16 "divmod"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v15,v23,v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 17 "middle opt"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v15,v23,v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 18 "known bits"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v15,v23,v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 19 "early fuse"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p1:1:0:2:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticLECall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticLECall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v15,v23,v9,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 20 "expand calls"
aux a17 nameoff "c+0" a3 0
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v15 SB t17 0 - p0:0:0:0:0 0 -
v v23 OffPtr t35 0 - p0:0:0:0:0 0 v2
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
v v9 LocalAddr t22 0 a4 p1:1:0:1:0 0 v2,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts 0=v23
freev v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 21 "decompose builtin"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v15 SB t17 0 - p0:0:0:0:0 0 -
v v23 OffPtr t35 0 - p0:0:0:0:0 0 v2
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
v v9 LocalAddr t22 0 a4 p1:1:0:1:0 0 v2,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts 0=v23
freev v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 22 "softfloat"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v15 SB t17 0 - p0:0:0:0:0 0 -
v v23 OffPtr t35 0 - p0:0:0:0:0 0 v2
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
v v9 LocalAddr t22 0 a4 p1:1:0:1:0 0 v2,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts 0=v23
freev v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 23 "branchelim"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
v v15 SB t17 0 - p0:0:0:0:0 0 -
v v23 OffPtr t35 0 - p0:0:0:0:0 0 v2
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 3 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
v v9 LocalAddr t22 0 a4 p1:1:0:1:0 0 v2,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts 0=v23
freev v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 24 "late opt"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 25 "dead auto elim"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 26 "sccp"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 27 "generic deadcode"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 28 "late fuse"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 29 "check bce"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 30 "dse"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 31 "memcombine"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 32 "writebarrier"
f b1 t1 a1 33 5
b b1 If p1:1:0:0:0 0 0 - v32 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 5 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v32 IsNonNil t5 0 - p1:1:0:1:0 1 v6
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 StaticCall t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 LocalAddr t22 0 a7 p20:104:9:2:0 2 v2,v1
v v16 Load t3 0 - p1:1:0:0:0 1 v6,v1
v v20 StaticCall t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 Load t4 0 - p20:104:2:0:0 1 v19,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 33 "lower"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 34 "addressing modes"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 35 "late lower"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 36 "pair"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 38 "lowered cse"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 39 "elim unread autos"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 41 "lowered deadcode"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 42 "checkLower"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 43 "loop invariant"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 45 "tighten"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
v v2 SP t17 0 - p0:0:0:0:0 2 -
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 46 "late deadcode"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
v v2 SP t17 0 - p0:0:0:0:0 2 -
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 47 "critical"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
v v2 SP t17 0 - p0:0:0:0:0 2 -
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 48 "phi tighten"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 0 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
v v2 SP t17 0 - p0:0:0:0:0 2 -
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 49 "likelyadjust"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
v v2 SP t17 0 - p0:0:0:0:0 2 -
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b3:b1,b5:b1
cache sdom b1:-:b3:-:2:17,b3:b1:-:b5:5:8,b5:b1:-:-:11:14
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
dcllen 7
end
pass 50 "layout"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b5:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
v v2 SP t17 0 - p0:0:0:0:0 2 -
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b5:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b5:b1:-:-:11:14,b3:b1:-:b5:5:8
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
fstate laidout
dcllen 7
end
pass 51 "schedule"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b5:0,b3:0 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b5:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b5:b1:-:-:11:14,b3:b1:-:b5:5:8
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
fstate scheduled,laidout
dcllen 7
end
pass 52 "late nilcheck"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b5:0,b3:0 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b5:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b5:b1:-:-:11:14,b3:b1:-:b5:5:8
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
fstate scheduled,laidout
dcllen 7
end
pass 53 "flagalloc"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b5:0,b3:0 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v19 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v19,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v9,v32,v23,v15,v8,v31,v30,v29,v28,v27,v10,v22,v18,v14,v13,v26,v25,v7,v5,v4,v3
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b5:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b5:b1:-:-:11:14,b3:b1:-:b5:5:8
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
fstate scheduled,laidout
dcllen 7
end
pass 54 "regalloc"
aux a1 call "AuxCall{main.(*SChan).Recv}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t4 a4 0 -1
callreg 0:1 - 0 -
aux a8 call "AuxCall{runtime.chanrecv2}" a9 1 2 1 8 16 2 1
abiparam in 0 t37 - 0 0
abiparam in 1 t22 - 1 8
abiparam out 0 t5 - 0 -1
callreg 0:1,1:2 0:1 7fffffff97ffffff -
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b5:0,b3:0 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v9 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v9,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v3,v4,v5,v7,v8,v10,v13,v14,v15,v18,v22,v23,v25,v26,v27,v28,v29,v30,v31,v32
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b5:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b5:b1:-:-:11:14,b3:b1:-:b5:5:8
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
fstate scheduled,laidout
regalloc 34 v2:SP,v6:R0,v9:R1,v16:R0,v20:[R0],v24:R0,v33:[]
dcllen 7
end
pass 55 "loop rotate"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b5:0,b3:0 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v9 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v9,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v3,v4,v5,v7,v8,v10,v13,v14,v15,v18,v22,v23,v25,v26,v27,v28,v29,v30,v31,v32
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b5:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b5:b1:-:-:11:14,b3:b1:-:b5:5:8
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
fstate scheduled,laidout
regalloc 34 v2:SP,v6:R0,v9:R1,v16:R0,v20:[R0],v24:R0,v33:[]
dcllen 7
end
pass 56 "trim"
f b1 t1 a1 33 5
b b1 ARM64NZ p1:1:0:1:0 1 0 - v6 b5:0,b3:0 -
v v6 ArgIntReg t2 0 a17 p1:1:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
b b5 Ret p1:1:0:1:0 0 0 - v33 - b1:0
v v2 SP t17 0 - p0:0:0:0:0 2 -
v v16 ARM64MOVDload t3 0 - p1:1:0:0:0 1 v6,v1
v v17 InlMark t32 15 - p1:1:0:0:0 0 v1
v v9 ARM64MOVDaddr t22 0 a7 p20:104:9:2:0 1 v2
v v20 ARM64CALLstatic t38 16 a8 p20:104:9:1:0 1 v16,v9,v1
v v21 SelectN t30 1 - p20:104:9:0:0 2 v20
v v24 ARM64MOVDload t4 0 a7 p20:104:2:0:0 1 v2,v21
v v33 MakeResult t41 0 - p1:1:0:1:0 1 v24,v21
b b3 Exit p1:1:0:0:0 0 0 - v12 - b1:1
v v11 ARM64CALLstatic t34 0 a10 p1:1:0:0:0 1 v1
v v12 SelectN t30 0 - p1:1:0:0:0 1 v11
names s1,s2,s3,s4
named s1 v6
named s2 v16
named s3 v24
named s4 v24
splits -
canon a3/t2/0/-/0=s1,a14/t3/0/-/0=s2,a15/t4/0/-/0=s3,a16/t4/0/-/0=s4
consts -
freev v3,v4,v5,v7,v8,v10,v13,v14,v15,v18,v22,v23,v25,v26,v27,v28,v29,v30,v31,v32
freeb b2,b4
cache postorder b5,b3,b1
cache idom b1:-,b5:b1,b3:b1
cache sdom b1:-:b3:-:2:17,b5:b1:-:-:11:14,b3:b1:-:b5:5:8
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a7:3,a17:4
cache linestarts 1:1:1,20:104:104
fstate scheduled,laidout
regalloc 34 v2:SP,v6:R0,v9:R1,v16:R0,v20:[R0],v24:R0,v33:[]
dcllen 7
end
frontend
end
ptrcache t3,t4,t7,t8,t9,t10,t12,t14,t15,t17,t18,t19,t26,t36,t40
typelink t30=t34,t39=t40
typeorder t6,t10,t7,t11,t8,t12,t9,t13,t4,t16,t17,t27,t28,t14,t15,t5,t19,t20,t21,t22,t23,t24,t25,t26,t35,t2,t36,t1,t37,t3,t39=t40,t18,t29,t30,t32,t31,t33,t34,t41,t38
eof
"#

/-- `test/closedchan/main/(*SChan).Recv,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "(*SChan).Recv" 1
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
type t1 8 8 8 1 01 "*SChan"
name n1 "c" PPARAM t1 1 "main.c" 0 a3
type t2 8 8 0 0 - "int"
name n2 "~r0" PPARAMOUT t2 1 "main.~r0" 0 a4
type t3 8 8 8 1 01 "SChan"
name n3 "c" PAUTO t3 1 "main.c" 0 a14
name n4 "~r0" PAUTO t2 1 "main.~r0" 0 a16
name n5 "x" PAUTO t2 1 "main.x" 0 a15
name n6 ".autotmp_5" PAUTO t3 3 "main..autotmp_5" 0 -
name n7 ".autotmp_6" PAUTO t2 3 "main..autotmp_6" 0 a7
in n1 0 used
in n2 0 outregs
in n3 0 used
in n4 0 -
in n5 0 used
in n6 0 used,autotmp
in n7 0 used,addrtaken,autotmp
out n1 0 used
out n7 -8 used,addrtaken,autotmp
opt n6 0 autotmp
opt n3 0 -
opt n5 0 -
opt n2 0 outregs
opt n4 0 -
stack 8 0 8
end
genin
posbase p1 "<autogenerated>" 1 1 -1 0 "<autogenerated>" "<autogenerated>" 1 1
sym y1 "main.(*SChan).Recv" 1
curfn p1:1:0:0:0 0 0
regargs 8192:0:t1
text y1 0 0 23 0 1 200091
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "main.(*SChan).Recv.arginfo1" 0
sym y5 "main.(*SChan).Recv.argliveinfo" 0
sym y6 "main..autotmp_6" 0
sym y7 "main.SChan.Recv" 1
inl i15 - p1:1:0:0:0 y7 "SChan.Recv"
posbase p20 "./closedchan.go" 1 1 15 1 "./closedchan.go" "./closedchan.go" 1 1
sym y8 "runtime.chanrecv2" 1
sym y9 "runtime.panicwrap" 1
sym y10 "type:string" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i8 0 0 p1:1:0:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p1:1:0:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p1:1:0:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p1:1:0:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p1:1:0:2:0
p 6 6 0 0 0 - CBZ 0 REG/8192/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@14 0 0 p1:1:0:1:0
p 7 7 0 0 0 - MOVD 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p1:1:0:2:0
p 8 8 0 0 0 - NOP 0 _ 0 - _ 0 0 p0:0:0:0:0
p 9 9 0 0 0 - MOVD 0 ADDR/8383/0/0/AUTO/0/-8/y6/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p20:104:9:1:0
p 10 10 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p20:104:9:1:0
p 11 11 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y8/- 0 0 p20:104:9:1:0
p 12 12 0 0 0 - MOVD 0 MEM/8383/0/0/AUTO/0/-8/y6/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p20:104:2:2:0
p 13 13 0 0 0 - RET 0 _ 0 - _ 0 0 p1:1:0:1:0
p 14 14 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y9/- 0 0 p1:1:0:2:0
p 15 15 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p1:1:0:0:0
p 16 16 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 23 0 1 200091
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
inlmark @6 15
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 1
reloc 0 0 R_USEIFACE 0 y10
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgslot 1 n3 t3 0
dbgslot 2 n5 t2 0
dbgslot 3 n4 t2 0
dbgvar 0 n1 0
dbgvar 1 n3 1
dbgvar 2 n5 2
dbgloc 0 1:-10000:5:16:50
dbgloc 1 5:16:5:20:50
dbgloc 2 5:24:3:-10000:50
dbgregout n2
dbgpc 5:16:8,5:20:12,5:24:13,3:-10000:14
end
asm
sym y11 "runtime.morestack_noctxt" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/48/-/i8 0 0 p1:1:0:0:0
p 17 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 18 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:0:0
p 19 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:0:0
p 20 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@29 0 0 p1:1:0:0:0
p 21 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p1:1:0:0:0
p 22 12 48 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-48/-/- 0 0 p1:1:0:0:1
p 23 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p1:1:0:0:0
p 24 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p1:1:0:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p1:1:0:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p1:1:0:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p1:1:0:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p1:1:0:2:0
p 6 24 0 0 85 - CBZ 0 REG/8192/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/14/-/@14 0 0 p1:1:0:1:0
p 7 28 0 0 333 - MOVD 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p1:1:0:2:0
p 8 32 0 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p0:0:0:0:0
p 9 32 0 0 325 - MOVD 0 ADDR/0/0/0/AUTO/32/-8/y6/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p20:104:9:1:0
p 10 36 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p20:104:9:1:0
p 11 36 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y8/- 0 0 p20:104:9:1:0
p 12 40 0 0 329 - MOVD 0 MEM/0/0/0/AUTO/47/-8/y6/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p20:104:2:2:0
p 13 44 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 25 48 -48 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/48/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 26 52 48 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p1:1:0:1:0
p 14 56 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y9/- 0 0 p1:1:0:2:0
p 15 60 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:0:0
p 27 64 -48 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:0:0
p 28 64 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p1:1:0:0:0
p 29 64 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:0:0
p 30 64 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p1:1:0:0:0
p 31 68 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 32 72 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y11/- 0 0 p1:1:0:0:0
p 33 76 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p1:1:0:0:0
p 34 76 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 35 80 48 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@17 0 0 p1:1:0:0:0
fn y1 8 40 23 0 1 200091
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
inlmark @6 15
funcaux y2 y3 - - y4 y5 -
text 96 0 900b40f9ff6330ebc9010054fe0f1df8fd831ff8fd2300d1000100b4000040f9e183009100000094e01340f9fd835ff8fe0743f8c0035fd6000000941f2003d5e00700f9e3031eaa00000094e00740f9ecffff17000000000000000000000000 4
reloc 0 0 R_USEIFACE 0 y10
reloc 36 4 R_CALLARM64 0 y8
reloc 56 4 R_CALLARM64 0 y9
reloc 72 4 R_CALLARM64 0 y11
pcln y16 y17 y18 y19 y12,y13,y14,y15 y2,y3,_,_,_,y4,y5
usedfiles 0,1
inltree 0 -1 p1:1:0:0:0 y7 "SChan.Recv" 24
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y12 SRODATA 11 1 28000 00010102020d0103020500 0
data y13 SRODATA 7 1 28000 00090407030800 0
data y14 SRODATA 0 1 28000 - 0
data y15 SRODATA 5 1 28000 0006041200 0
data y16 SRODATA 11 1 28000 020460095f0160025f0800 0
data y17 SRODATA 7 1 28000 02080203010d00 0
data y18 SRODATA 9 1 28000 0408ce0103cd010d00 0
data y19 SRODATA 7 1 28000 00080203010d00 0
end
dwarf
sym y20 "" 0
sym y21 "" 0
sym y22 "" 0
sym y23 "" 0
posbase p2 "./closedchan.go" 1 1 -1 1 "./closedchan.go" "./closedchan.go" 1 1
sym y24 "go:info.main.SChan.Recv$abstract" 0
sym y25 "go:info.*main.SChan" 0
sym y26 "go:info.int" 0
sym y27 "go:info.main.SChan" 0
sym y28 "type:int" 0
dwfn y20 y21 y22 - y23 "main.(*SChan).Recv" 0:1 1 1 1 74
dwdcl n1,n7
dwclosure 0 -
dwparents -
dwparams n1,n2
dwinlfn y7 y24
dwinldcl y7 "c" 0 p2:102:7:0:0
dwinldcl y7 "~r0" 0 p2:102:23:0:0
dwinldcl y7 "x" 0 p2:104:7:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "*main.SChan" 0 0 1 p2:102:7:0:0
dwname n7 1 1 1 0 0 0 -8 0 - - ? 0 0 ? p20:104:2:0:0
dwname n6 1 0 1 0 0 0 0 0 - - "main.SChan" 0 0 1 p20:104:2:0:0
dwname n3 1 0 0 1 0 0 0 0 - - "main.SChan" 0 0 1 p20:102:7:0:0
dwname n5 1 0 0 0 1 0 0 0 - - "int" 0 0 1 p20:104:7:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "int" 0 0 1 p2:102:23:0:0
dwname n4 1 0 0 1 0 0 0 0 - - "int" 0 0 1 p20:102:23:0:0
var 0 0 "c" 5 1 0 0 0 8 y25 "./closedchan.go" 102 7 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y26 "./closedchan.go" 102 23 0 1 0 0 -
var 2 0 "c" 5 1 0 1 0 -8 y27 "./closedchan.go" 102 7 16 0 1 0 v1
var 3 0 "x" 52 1 0 0 0 -8 y26 "./closedchan.go" 104 7 16 2 1 0 v2
scope 0 0 - 0,1,2,3
inlcall 0 15 0:1 y24 - 1 32:44 2,3
dieref y20 8 y24 0
dieref y20 10 y24 2
data y20 SDWARFFCN 85 0 0 046d61696e2e282a534368616e292e5265637600000060019c012d6300006600000000000000002e7e7230000166000000000009000000000000000001000000012900000000000000002300000000000000000000 12
reloc 0 0 R_USETYPE 0 y28
reloc 0 0 R_USETYPE 0 y10
reloc 20 2 R_DWTXTADDR_U2 0 y1
reloc 31 4 R_DWARFSECREF 0 y25
reloc 35 4 R_DWARFSECREF 0 y21
reloc 46 4 R_DWARFSECREF 0 y26
reloc 52 4 R_DWARFSECREF 0 y24
reloc 56 4 R_DWARFSECREF 0 y22
reloc 66 4 R_DWARFSECREF 0 y24
reloc 70 4 R_DWARFSECREF 9 y21
reloc 75 4 R_DWARFSECREF 0 y24
reloc 79 4 R_DWARFSECREF 18 y21
data y21 SDWARFLOC 27 0 0 010000040020015000010000042028015000010000042c38015000 3
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
reloc 19 2 R_DWTXTADDR_U2 0 y1
data y22 SDWARFRANGE 7 0 0 01000004202c00 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y23 SDWARFLINES 40 0 0 00090200000000000000000a8706af04020603e2003c065f040106039d7f33068706370224000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded `(*SChan).Recv` (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG24` gives (`b5`: the no-code `v2`; `v16`'s `MOVD`; `v9`'s `MOVD
$var`; the `CALL`, `v24`'s `MOVD`). -/
def tab : PcTab := [(1, [5, 5, 5]), (5, [7, 7, 8, 8, 10, 12, 12, 13, 13]), (3, [14, 15, 15])]

/-- The class table `checkG24` gives (`R0` at class 64 in `b5` and `b3`). -/
def kt : KTab := (match checkG24 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk5 : Block := (lc.ctx.f.block? 5).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 32-byte frame with 8 bytes of extra
space, every symbol at `symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 32 8 ps.toList

/-- `ι`: GenG2's, and `.autotmp_6`'s block of activation 0 at `SP + 16`. -/
def ι24 (b : Blk) : Option (BitVec 64) :=
  if b = .temp 0 7 then some (GenG2.sp0 + 16) else GenG2.ι b

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0), no home slot,
the PC table of `checkG24`. -/
def E : MatchEnv :=
  { lc, ι := ι24, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The empty memory. -/
def mem0 : Mem := {}

/-- The `runLoc` state before `v2`: `c = 5` in `R0`, every other register `poison`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w64 5 else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v2`: `X0 = 5`, the activation's `g` and `FP`, the PC of `v2`, a zero
memory. -/
def m0 : MState :=
  { x := fun k => if k = 0 then 5 else if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8
      else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 5 0, mem := fun _ => 0 }

/-- The register holds `SP`'s value at its `uintptr` shape: the pointer to the start of activation
0's outgoing-argument block as a word (`Ptr.word`), `2^62`. -/
def isSP : Option Val → Bool
  | some (.int .w64 x) => x == 0x4000000000000000
  | _ => false

theorem isSP_spec {o : Option Val} (h : isSP o = true) :
    o = some (.int .w64 0x4000000000000000) := by
  unfold isSP at h
  split at h
  · simp only [beq_iff_eq] at h
    rw [h]
  · cases h

/-- What compiled evaluation checks on `(*SChan).Recv`: `checkG24` accepts it with `tab` and `kt`
and `checkG23` does not; the only accessed frame variable is `.autotmp_6` (aux 7), operand `-8`,
`NAME_AUTO`, of activation 0, at `frameOff 16`; there is no home slot; `b5` holds `v2` (`SP`) at
index 0, `R0` has class 64 there; `stepLoc` runs `v2` from `s0` to a state whose Go register `SP`
holds `SP`'s value. -/
def gFacts : Bool :=
  (checkG24 lc ps bs g).toOption == some (tab, kt) && (checkG23 lc ps bs g).toOption.isNone &&
    accessedVars lc == [7] && varOp g 7 == some (.AUTO, -8) && lc.ctx.act == 0 &&
    (homeSlots lc).isEmpty && decide (frameOff L .AUTO (-8) = 16) &&
    lc.ctx.f.blocks.toList.contains 5 && (lc.ctx.f.block? 5).isSome &&
    (lc.ctx.f.value? 2).isSome && blk5.values[0]? == some 2 && (val 2).op == .SP &&
    (kAt lc kt 5 blk5 0).get 0 == some 64 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 2)) (fun s1 => isSP s1.regs[30]?)

theorem g24_facts : gFacts = true := by
  native_decide

/-- The facts of `g24_facts` as hypotheses. -/
theorem facts :
    checkG24 lc ps bs g = .ok (tab, kt) ∧ accessedVars lc = [7] ∧ varOp g 7 = some (.AUTO, -8) ∧
      lc.ctx.act = 0 ∧ (homeSlots lc).isEmpty = true ∧ frameOff L .AUTO (-8) = 16 ∧
      5 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 5 = some blk5 ∧
      lc.ctx.f.value? 2 = some (val 2) ∧ blk5.values[0]? = some 2 ∧ (val 2).op = .SP ∧
      (kAt lc kt 5 blk5 0).get 0 = some 64 ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 2)) (fun s1 => isSP s1.regs[30]?) = true := by
  have hf := g24_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hvo⟩, hact⟩, hsl⟩, hoff⟩, hm5⟩, hb5s⟩, hv2s⟩, hi0⟩,
    hop2⟩, hk0⟩, hrun⟩ := hf
  refine ⟨?_, hav, hvo, hact, hsl, hoff, hm5, ?_, ?_, hi0, hop2, hk0, hrun⟩
  · revert hres; cases checkG24 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb5s
    simp [blk5, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv2s
    simp [val, hv]

theorem ι24_temp : ι24 (.temp 0 7) = some (GenG2.sp0 + 16) := by simp [ι24]

theorem ι24_ne {b : Blk} (h : b ≠ .temp 0 7) : ι24 b = GenG2.ι b := by simp [ι24, h]

theorem addrAgree24 : AddrAgree ι24 := by
  intro b n a hb ha hnt
  rw [ι24_ne (hnt 0 7)] at ha
  exact GenG2.addrAgree b n a hb ha hnt

theorem g24Env (hc : checkG24 lc ps bs g = .ok (tab, kt)) (hvs : accessedVars lc = [7])
    (hvo : varOp g 7 = some (.AUTO, -8)) (hact : lc.ctx.act = 0)
    (hsl : (homeSlots lc).isEmpty = true) (hoff : frameOff L .AUTO (-8) = 16) :
    G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG24_spec hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := addrAgree24
        glob := fun _ _ _ _ => by simp [E, ι24, GenG2.ι]; rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG24_spec hc
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
        show ι24 (.temp 0 7) = some (GenG2.sp0 + BitVec.ofInt 64 16)
        rw [ι24_temp]
        rfl }
    wbs := fun h => by cases h }
  icalls := fun h => by cases h

theorem memInj0 (mm : Memory) : MemInj ι24 mem0 mm where
  nil := by simp [ι24, GenG2.ι]
  mapped := by intro b al h; simp [mem0] at h
  inj := by intro b al b' al' a a' h; simp [mem0] at h
  bytes := ⟨fun _ _ => False, by intro b al a h; simp [mem0] at h⟩

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w64 5) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 5 0 m0 where
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
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g24Inv0 (h0 : (kAt lc kt 5 blk5 0).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 5 blk5 0) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v2`, `SP`: none apply. -/
theorem pre2 {s : LocState} (hop : (val 2).op = .SP) : G14Pre lc s (val 2) := by
  have hne : ∀ o : Op, o ≠ .SP → (val 2).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G24 on `(*SChan).Recv`**: from the state before `v2` with `c = 5` in `R0` (`X0 = 5`),
`g24_value` runs `SP` (`v2`, which `checkG23` rejects after the entry values): `runLoc`'s Go
register `SP` holds `SP`'s value at its `uintptr` shape (`2^62`), and the machine state related to
it before `v16`, under an activation extending `E`, is at `v2`'s PC: no code ran. -/
theorem genG24_value_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 2) = .ok s1 ∧
      s1.regs[30]? = some (.int .w64 0x4000000000000000) ∧
      E.Extends E1 ∧ G10Env lc g L ps 0 tab E1 ∧
      PStar GenG2.H0 L ps.toList 0 m0 m1 ∧ LocMatch E1 s1 5 1 m1 ∧ m1.pc = m0.pc := by
  obtain ⟨hc, hvs, hvo, hact, hsl, hoff, hm5, hb, hv2, hi0, hop2, hk0, hrun⟩ := facts
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hE := g24Env hc hvs hvo hact hsl hoff
  have hne : ∀ o : Op, o ≠ .SP → (val 2).op ≠ o := fun o h h' => h (h'.symm.trans hop2)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g24_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm5 hb hi0 hv2 (by rw [hop2]; rfl) locMatch0 (g24Inv0 hk0) (by trivial)
    (pre2 hop2)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop2]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  refine ⟨s1, E1, m1, hs1, isSP_spec hr1, hx1, hE1, hp1, hm1', ?_⟩
  rw [hm1'.pc, hx1.1]
  rfl

end GoFV.Proof.Witness.GenG24
