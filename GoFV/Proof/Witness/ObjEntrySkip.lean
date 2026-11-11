import GoFV.Proof.Obj.EntrySkip
import GoFV.Proof.Witness.GenG2

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: entry stores after spills and values without code (`entrySkip`)

`std/std/fmt/Sscan,1.ssa` and `std/std/fmt/Sscan,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`): `func Sscan(str
string, a ...any) (n int, err error)`. Its entry block holds the five `ArgIntReg`s (`entryLen` is
5), then the spills `v35`, `v38`, `v25` (`StoreReg`), `v3 = SB`, `v2 = SP`, `v1 = InitMem`, and
then the entry store `v39 = STP (R0, R1), str+0(FP)` of the register-assigned parameter `str`, whose
window `[0, 16)` the function accesses (`pendWins`). `storesFrom` steps over the spills and the
values without code (`entrySkip`), so `entryStoresOK lc g (entryLen lc)` holds; the entry stores
as long as they last from `entryLen lc` without that step (`storesFromNoSkip`, `storesFrom`
before it) are none, and that check fails. `checkG66` accepts the function. By compiled
evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `skip_facts`):
`entrySkip_witness`.
-/

namespace GoFV.Proof.Witness.ObjEntrySkip

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

/-- `std/std/fmt/Sscan,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "fmt"
func "Sscan" 1 0 0
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
config localpkg "fmt"
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
type t4 INTER 16 8 16 hasptr,comparable,named,emptyiface "any" "interface {}"
type t3 SLICE 24 8 8 hasptr "[]any" "[]interface {}" t4
type t5 INT 8 8 0 comparable,named "int" "int"
type t6 INTER 16 8 16 hasptr,comparable,named "error" "error"
type t1 FUNC 8 8 8 hasptr,direct,variadic "func(string, ...any) (int, error)" "func(string, ...interface {}) (int, error)" 0 2 2
field 0 "str" t2 ? 0
field 1 "a" t3 ? 0
field 2 "n" t5 ? 0
field 3 "err" t6 ? 0
aux a2 sym "fmt.Sscan" "fmt.Sscan" 1 - 0 - - - - 0
posbase p23 "fmt/scan.go" 1 1 -1
aux a3 name "str" "str" PPARAM t2 0 2 addrtaken,used p23:99:12:0:0
aux a4 name "a" "a" PPARAM t3 16 1 used p23:99:24:0:0
aux a5 name "n" "n" PPARAMOUT t5 0 1 - p23:99:35:0:0
aux a6 name "err" "err" PPARAMOUT t6 0 1 - p23:99:42:0:0
aux a1 call "AuxCall{fmt.Sscan}" a2 1 2 2 8 40 5 3
abiparam in 0 t2 a3 0,1 0
abiparam in 1 t3 a4 2,3,4 16
abiparam out 0 t5 a5 0 -1
abiparam out 1 t6 a6 1,2 -1
type t7 BOOL 1 1 0 comparable,named "bool" "bool"
type t8 INT8 1 1 0 comparable,named "int8" "int8"
type t9 INT16 2 2 0 comparable,named "int16" "int16"
type t10 INT32 4 4 0 comparable,named "int32" "int32"
type t11 INT64 8 8 0 comparable,named "int64" "int64"
type t12 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t13 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t14 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t15 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t16 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t17 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t18 UINT 8 8 0 comparable,named "uint" "uint"
type t19 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t12
type t21 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t10
type t22 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t14
type t23 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t5
type t24 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t19
type t25 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t16
type t26 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t17
type t27 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t20
type t28 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t29 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t30 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t31 SSA ? ? ? - "mem" ""
type t32 SSA ? ? ? - "flags" ""
type t33 SSA ? ? ? - "void" ""
type t34 SSA 16 8 ? - "int128" ""
type t35 RESULTS ? ? ? - "mem" "" 1 t31
type t36 PTR 8 8 8 hasptr,direct,comparable "*string" "*string" t2
type t37 PTR 8 8 8 hasptr,direct,comparable "*[]any" "*[]interface {}" t3
type t38 PTR 8 8 8 hasptr,direct,comparable "*error" "*error" t6
aux a7 type "string" t2
aux a8 sym "type:string" "type:string" 0 - 0 - t2 - - 0
rtype 16 8 -125357384 24 "runtime.gcbits.0100000000000000" ""
type t39 RESULTS ? ? ? - "*string,mem" "" 2 t36,t31
aux a10 sym "runtime.mallocgcSmallScanNoHeaderSC2" "runtime.mallocgcSmallScanNoHeaderSC2" 1 - 0 - - - - 0
aux a9 call "AuxCall{runtime.mallocgcSmallScanNoHeaderSC2}" a10 1 3 1 8 24 3 1
abiparam in 0 t19 - 0 0
abiparam in 1 t20 - 1 8
abiparam in 2 t7 - 2 16
abiparam out 0 t36 - 0 -1
type t41 STRING 16 8 8 hasptr,comparable,named "stringReader" "fmt.stringReader"
type t40 PTR 8 8 8 hasptr,direct,comparable "*stringReader" "*fmt.stringReader" t41
aux a11 sym "go:itab.*fmt.stringReader,io.Reader" "go:itab.*fmt.stringReader,io.Reader" 0 SRODATA 32 dupok,contentaddressable - t40 00000000000000000000000000000000e8559db8000000000000000000000000 3
reloc 0 8 R_ADDR 0 "type:io.Reader" 0
reloc 8 8 R_ADDR 0 "type:*fmt.stringReader" 0
reloc 24 8 RelocType(-32767) 0 "fmt.(*stringReader).Read" 1
type t42 INTER 16 8 16 hasptr,comparable,named "io.Reader" "io.Reader"
type t43 RESULTS ? ? ? - "int,error,mem" "" 3 t5,t6,t31
aux a13 sym "fmt.Fscan" "fmt.Fscan" 1 - 0 - - - - 0
aux a12 call "AuxCall{fmt.Fscan}" a13 1 2 2 8 40 5 3
abiparam in 0 t42 - 0,1 0
abiparam in 1 t3 - 2,3,4 16
abiparam out 0 t5 - 0 -1
abiparam out 1 t6 - 1,2 -1
slot s1 a4 t3 0 - 0
aux a14 name "&str" "&str" PAUTO t36 0 0 used p23:99:12:0:0
slot s2 a14 t36 0 - 0
f b1 t1 a1 28 1
typs Bool=t7,Int8=t8,Int16=t9,Int32=t10,Int64=t11,UInt8=t12,UInt16=t13,UInt32=t14,UInt64=t15,Int=t5,Float32=t16,Float64=t17,UInt=t18,Uintptr=t19,String=t2,BytePtr=t20,Int32Ptr=t21,UInt32Ptr=t22,IntPtr=t23,UintptrPtr=t24,Float32Ptr=t25,Float64Ptr=t26,BytePtrPtr=t27,Complex64=t28,Complex128=t29,UnsafePtr=t30,Mem=t31,Flags=t32,Void=t33,Int128=t34,ResultMem=t35
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v2 SP t19 0 - p0:0:0:0:0 4 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v5 LocalAddr t37 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t23 0 a5 p0:0:0:0:0 0 v2,v1
v v7 LocalAddr t38 0 a6 p0:0:0:0:0 0 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:0:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v11 Const64 t5 0 - p0:0:0:0:0 0 -
v v12 ConstInterface t6 0 - p0:0:0:0:0 0 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v20 Copy t40 0 - p23:100:31:2:0 1 v18
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v20
v v23 StaticLECall t43 40 a12 p23:100:14:0:0 4 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v25 SelectN t5 0 - p23:100:14:0:0 0 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 0=v11,1=v15,16=v14,2233445566=v12
freev -
freeb -
dcllen 10
end
pass 1 "number lines"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v2 SP t19 0 - p0:0:0:0:0 4 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v5 LocalAddr t37 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t23 0 a5 p0:0:0:0:0 0 v2,v1
v v7 LocalAddr t38 0 a6 p0:0:0:0:0 0 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v11 Const64 t5 0 - p0:0:0:0:0 0 -
v v12 ConstInterface t6 0 - p0:0:0:0:0 0 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v20 Copy t40 0 - p23:100:31:2:0 1 v18
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v20
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 4 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v25 SelectN t5 0 - p23:100:14:0:0 0 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 0=v11,1=v15,16=v14,2233445566=v12
freev -
freeb -
cache postorder b1
cache linestarts 23:99:100
dcllen 10
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 5 -
v v2 SP t19 0 - p0:0:0:0:0 4 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v5 LocalAddr t37 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t23 0 a5 p0:0:0:0:0 0 v2,v1
v v7 LocalAddr t38 0 a6 p0:0:0:0:0 0 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v11 Const64 t5 0 - p0:0:0:0:0 0 -
v v12 ConstInterface t6 0 - p0:0:0:0:0 0 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v20 Copy t40 0 - p23:100:31:2:0 0 v18
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 4 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v25 SelectN t5 0 - p23:100:14:0:0 0 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 0=v11,1=v15,16=v14,2233445566=v12
freev -
freeb -
cache postorder b1
cache linestarts 23:99:100
dcllen 10
end
pass 3 "early deadcode"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache linestarts 23:99:100
dcllen 10
end
pass 4 "short circuit"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache linestarts 23:99:100
dcllen 10
end
pass 5 "decompose user"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache linestarts 23:99:100
dcllen 10
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache linestarts 23:99:100
dcllen 10
end
pass 7 "opt"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache linestarts 23:99:100
dcllen 10
end
pass 8 "zero arg cse"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache linestarts 23:99:100
dcllen 10
end
pass 9 "opt deadcode"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache linestarts 23:99:100
dcllen 10
end
pass 10 "generic cse"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
end
pass 11 "phiopt"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
end
pass 12 "gcse deadcode"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
end
pass 13 "nilcheckelim"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
end
pass 14 "prove"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
end
pass 15 "divisible"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
end
pass 16 "divmod"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
end
pass 17 "middle opt"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
end
pass 18 "known bits"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
end
pass 19 "early fuse"
f b1 t1 a1 28 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v8 Arg t2 0 a3 p23:99:6:2:0 1 -
v v10 Arg t3 0 a4 p23:99:6:2:0 1 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v16 StaticLECall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticLECall t43 40 a12 p23:100:14:1:0 3 v22,v10,v19
v v24 SelectN t31 2 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:2:0:0 1 v23
v v27 SelectN t6 1 - p23:100:2:0:0 1 v23
v v28 MakeResult t43 0 - p23:100:2:0:0 1 v26,v27,v24
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v25,v20,v12,v11,v7,v6,v5
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
end
pass 20 "expand calls"
type t44 RESULTS ? ? ? - "int,unsafe.Pointer,unsafe.Pointer,mem" "" 4 t5,t30,t30,t31
aux a15 nameoff "str+0" a3 0
aux a16 nameoff "str+8" a3 8
type t45 PTR 8 8 8 hasptr,direct,comparable "*any" "*interface {}" t4
aux a17 nameoff "a+0" a4 0
aux a18 nameoff "a+8" a4 8
aux a19 nameoff "a+16" a4 16
f b1 t1 a1 37 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 5 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v8 StringMake t2 0 - p23:100:2:2:0 1 v20,v12
v v10 SliceMake t3 0 - p23:100:2:2:0 3 v7,v6,v5
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 2 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a7 p23:99:6:1:0 1 v4,v8,v1
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v22 IMake t42 0 - p23:100:30:0:0 1 v21,v18
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v31,v18,v32,v33,v34,v19
v v24 SelectN t31 3 - p23:100:14:0:0 3 v23
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v27 IMake t6 0 - p23:100:14:2:0 1 v29,v30
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v37,v30,v24
v v25 OffPtr t36 0 - p0:0:0:0:0 0 v2
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v11 OffPtr t37 0 - p0:0:0:0:0 0 v2
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 2 v23
v v31 ITab t19 0 - p23:100:14:1:0 1 v22
v v32 SlicePtr t45 0 - p23:100:14:1:0 1 v10
v v33 SliceLen t5 0 - p23:100:14:2:0 1 v10
v v34 SliceCap t5 0 - p23:100:14:2:0 1 v10
v v35 LocalAddr t23 0 a5 p23:100:2:0:0 0 v2,v24
v v36 LocalAddr t38 0 a6 p23:100:2:0:0 0 v2,v24
v v37 ITab t19 0 - p23:100:2:0:0 1 v27
names s1,s2
named s1 v10
named s2 v18
splits -
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 0=v25,v11,1=v15,16=v14
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 21 "decompose builtin"
aux a20 type "int" t5
aux a21 type "*uint8" t20
slot s3 a4 t45 0 - 0
slot s4 a4 t5 8 - 0
slot s5 a4 t5 16 - 0
f b1 t1 a1 39 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 5 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v8 StringMake t2 0 - p23:100:2:2:0 0 v20,v12
v v10 SliceMake t3 0 - p23:100:2:2:0 0 v7,v6,v5
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 3 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 2 v3
v v9 Store t31 0 a20 p23:99:6:1:0 1 v38,v12,v39
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v22 IMake t42 0 - p23:100:30:0:0 0 v21,v18
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v24 SelectN t31 3 - p23:100:14:0:0 3 v23
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v27 IMake t6 0 - p23:100:14:2:0 0 v29,v30
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v25 OffPtr t36 0 - p0:0:0:0:0 0 v2
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 2 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 2 -
v v11 OffPtr t37 0 - p0:0:0:0:0 0 v2
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 2 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 2 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 2 -
v v29 SelectN t19 1 - p23:100:14:1:0 2 v23
v v30 SelectN t20 2 - p23:100:14:2:0 2 v23
v v35 LocalAddr t23 0 a5 p23:100:2:0:0 0 v2,v24
v v36 LocalAddr t38 0 a6 p23:100:2:0:0 0 v2,v24
v v38 OffPtr t23 8 - p23:99:6:1:0 1 v4
v v39 Store t31 0 a21 p23:99:6:1:0 1 v4,v20,v1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 0=v25,v11,1=v15,16=v14
freev v37,v34,v33,v32,v31
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 22 "softfloat"
f b1 t1 a1 39 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 5 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v8 StringMake t2 0 - p23:100:2:2:0 0 v20,v12
v v10 SliceMake t3 0 - p23:100:2:2:0 0 v7,v6,v5
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 3 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 2 v3
v v9 Store t31 0 a20 p23:99:6:1:0 1 v38,v12,v39
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v22 IMake t42 0 - p23:100:30:0:0 0 v21,v18
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v24 SelectN t31 3 - p23:100:14:0:0 3 v23
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v27 IMake t6 0 - p23:100:14:2:0 0 v29,v30
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v25 OffPtr t36 0 - p0:0:0:0:0 0 v2
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 2 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 2 -
v v11 OffPtr t37 0 - p0:0:0:0:0 0 v2
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 2 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 2 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 2 -
v v29 SelectN t19 1 - p23:100:14:1:0 2 v23
v v30 SelectN t20 2 - p23:100:14:2:0 2 v23
v v35 LocalAddr t23 0 a5 p23:100:2:0:0 0 v2,v24
v v36 LocalAddr t38 0 a6 p23:100:2:0:0 0 v2,v24
v v38 OffPtr t23 8 - p23:99:6:1:0 1 v4
v v39 Store t31 0 a21 p23:99:6:1:0 1 v4,v20,v1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 0=v25,v11,1=v15,16=v14
freev v37,v34,v33,v32,v31
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 23 "branchelim"
f b1 t1 a1 39 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 5 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v8 StringMake t2 0 - p23:100:2:2:0 0 v20,v12
v v10 SliceMake t3 0 - p23:100:2:2:0 0 v7,v6,v5
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 3 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 2 v3
v v9 Store t31 0 a20 p23:99:6:1:0 1 v38,v12,v39
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v22 IMake t42 0 - p23:100:30:0:0 0 v21,v18
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v24 SelectN t31 3 - p23:100:14:0:0 3 v23
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v27 IMake t6 0 - p23:100:14:2:0 0 v29,v30
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v25 OffPtr t36 0 - p0:0:0:0:0 0 v2
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 2 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 2 -
v v11 OffPtr t37 0 - p0:0:0:0:0 0 v2
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 2 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 2 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 2 -
v v29 SelectN t19 1 - p23:100:14:1:0 2 v23
v v30 SelectN t20 2 - p23:100:14:2:0 2 v23
v v35 LocalAddr t23 0 a5 p23:100:2:0:0 0 v2,v24
v v36 LocalAddr t38 0 a6 p23:100:2:0:0 0 v2,v24
v v38 OffPtr t23 8 - p23:99:6:1:0 1 v4
v v39 Store t31 0 a21 p23:99:6:1:0 1 v4,v20,v1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 0=v25,v11,1=v15,16=v14
freev v37,v34,v33,v32,v31
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 24 "late opt"
f b1 t1 a1 39 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 3 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a20 p23:99:6:1:0 1 v38,v12,v39
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v38 OffPtr t23 8 - p23:99:6:1:0 1 v4
v v39 Store t31 0 a21 p23:99:6:1:0 1 v4,v20,v1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v36,v35,v11,v25,v27,v22,v10,v8,v37,v34,v33,v32,v31
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 25 "dead auto elim"
f b1 t1 a1 39 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 3 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a20 p23:99:6:1:0 1 v38,v12,v39
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v38 OffPtr t23 8 - p23:99:6:1:0 1 v4
v v39 Store t31 0 a21 p23:99:6:1:0 1 v4,v20,v1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v36,v35,v11,v25,v27,v22,v10,v8,v37,v34,v33,v32,v31
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 26 "sccp"
f b1 t1 a1 39 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 3 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a20 p23:99:6:1:0 1 v38,v12,v39
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v38 OffPtr t23 8 - p23:99:6:1:0 1 v4
v v39 Store t31 0 a21 p23:99:6:1:0 1 v4,v20,v1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v36,v35,v11,v25,v27,v22,v10,v8,v37,v34,v33,v32,v31
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 27 "generic deadcode"
f b1 t1 a1 39 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 3 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a20 p23:99:6:1:0 1 v38,v12,v39
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v38 OffPtr t23 8 - p23:99:6:1:0 1 v4
v v39 Store t31 0 a21 p23:99:6:1:0 1 v4,v20,v1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v36,v35,v11,v25,v27,v22,v10,v8,v37,v34,v33,v32,v31
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 28 "late fuse"
f b1 t1 a1 39 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 3 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a20 p23:99:6:1:0 1 v38,v12,v39
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v38 OffPtr t23 8 - p23:99:6:1:0 1 v4
v v39 Store t31 0 a21 p23:99:6:1:0 1 v4,v20,v1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v36,v35,v11,v25,v27,v22,v10,v8,v37,v34,v33,v32,v31
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 29 "check bce"
f b1 t1 a1 39 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 3 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a20 p23:99:6:1:0 1 v38,v12,v39
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v38 OffPtr t23 8 - p23:99:6:1:0 1 v4
v v39 Store t31 0 a21 p23:99:6:1:0 1 v4,v20,v1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v36,v35,v11,v25,v27,v22,v10,v8,v37,v34,v33,v32,v31
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 30 "dse"
f b1 t1 a1 39 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 3 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a20 p23:99:6:1:0 1 v38,v12,v39
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v38 OffPtr t23 8 - p23:99:6:1:0 1 v4
v v39 Store t31 0 a21 p23:99:6:1:0 1 v4,v20,v1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v36,v35,v11,v25,v27,v22,v10,v8,v37,v34,v33,v32,v31
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 31 "memcombine"
f b1 t1 a1 39 1
b b1 Ret p23:100:2:1:0 0 0 - v28 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 2 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 3 v2,v1
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v9 Store t31 0 a20 p23:99:6:1:0 1 v38,v12,v39
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v17 SelectN t31 1 - p23:99:6:0:0 1 v16
v v18 SelectN t36 0 - p23:99:6:0:0 2 v16
v v19 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v17
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v38 OffPtr t23 8 - p23:99:6:1:0 1 v4
v v39 Store t31 0 a21 p23:99:6:1:0 1 v4,v20,v1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 1=v15,16=v14
freev v36,v35,v11,v25,v27,v22,v10,v8,v37,v34,v33,v32,v31
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 32 "writebarrier"
aux a22 sym "runtime.writeBarrier" "runtime.writeBarrier" 0 - 0 - - - - 0
aux a24 sym "runtime.wbMove" "runtime.wbMove" 1 - 0 - - - - 0
aux a23 call "AuxCall{runtime.wbMove}" a24 1 3 0 8 24 3 0
abiparam in 0 t19 - 0 0
abiparam in 1 t19 - 1 8
abiparam in 2 t19 - 2 16
f b1 t1 a1 39 3
b b1 If p23:99:6:0:0 -1 0 - v25 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 Const64 t19 16 - p0:0:0:0:0 1 -
v v15 ConstBool t7 1 - p0:0:0:0:0 1 -
v v13 Addr t20 0 a8 p0:0:0:0:0 1 v3
v v21 Addr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v36 Addr t22 0 a22 p23:100:2:1:0 1 v3
v v35 Const32 t14 0 - p0:0:0:0:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 4 v2,v1
v v38 OffPtr t23 8 - p23:99:6:1:0 1 v4
v v39 Store t31 0 a21 p23:99:6:1:0 1 v4,v20,v1
v v9 Store t31 0 a20 p23:99:6:1:0 1 v38,v12,v39
v v16 StaticCall t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 Load t14 0 - p23:99:6:0:0 1 v36,v17
v v25 Neq32 t7 0 - p23:99:6:0:0 1 v11,v35
v v27 Addr t19 0 a8 p23:99:6:0:0 1 v3
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 StaticCall t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 1 v17,v10
v v37 Move t31 16 a7 p23:99:6:0:0 1 v18,v4,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 StaticCall t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts 0=v35,1=v15,16=v14
freev v34,v33,v32,v31
freeb -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 33 "lower"
type t46 SSA 16 8 ? - "vec128" ""
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v39 ARM64MOVDstore t31 0 a3 p23:99:6:1:0 1 v34,v20,v1
v v9 ARM64MOVDstore t31 8 a3 p23:99:6:1:0 1 v34,v12,v39
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 4 v2,v1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v33,v25,v38,v35,v36,v31
freeb -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100:100=1
dcllen 10
zvar v7:1
end
pass 34 "addressing modes"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v39 ARM64MOVDstore t31 0 a3 p23:99:6:1:0 1 v34,v20,v1
v v9 ARM64MOVDstore t31 8 a3 p23:99:6:1:0 1 v34,v12,v39
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 4 v2,v1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v33,v25,v38,v35,v36,v31
freeb -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100:100=1
dcllen 10
zvar v7:1
end
pass 35 "late lower"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v39 ARM64MOVDstore t31 0 a3 p23:99:6:1:0 1 v34,v20,v1
v v9 ARM64MOVDstore t31 8 a3 p23:99:6:1:0 1 v34,v12,v39
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 4 v2,v1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v33,v25,v38,v35,v36,v31
freeb -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 36 "pair"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v9 Copy t31 0 - p23:99:6:1:0 1 v39
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v9
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v33,v25,v38,v35,v36,v31
freeb -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 38 "lowered cse"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 39 "elim unread autos"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 41 "lowered deadcode"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 42 "checkLower"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 43 "loop invariant"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 45 "tighten"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 46 "late deadcode"
f b1 t1 a1 39 3
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 47 "critical"
f b1 t1 a1 39 4
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b4:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
b b3 Ret p23:100:2:1:0 0 0 - v28 - b4:0,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
b b4 Plain p23:99:6:0:0 0 0 - - b3:0 b1:1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 48 "phi tighten"
f b1 t1 a1 39 4
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b4:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
b b3 Ret p23:100:2:1:0 0 0 - v28 - b4:0,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
b b4 Plain p23:99:6:0:0 0 0 - - b3:0 b1:1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 49 "likelyadjust"
f b1 t1 a1 39 4
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b4:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
b b3 Ret p23:100:2:1:0 0 0 - v28 - b4:0,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
b b4 Plain p23:99:6:0:0 0 0 - - b3:0 b1:1
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b2:b1,b3:b1,b4:b1
cache sdom b1:-:b4:-:2:23,b2:b1:-:b3:11:14,b3:b1:-:-:17:20,b4:b1:-:b2:5:8
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
dcllen 10
zvar v7:1
end
pass 50 "layout"
f b1 t1 a1 39 4
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b4:0 -
v v2 SP t19 0 - p0:0:0:0:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v34 SPanchored t19 0 - p0:0:0:0:0 3 v2,v1
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v34,v20,v12,v1
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
b b4 Plain p23:99:6:0:0 0 0 - - b3:0 b1:1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v34
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
b b3 Ret p23:100:2:1:0 0 0 - v28 - b4:0,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v34,v8
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
fstate laidout
dcllen 10
zvar v7:1
end
pass 51 "schedule"
f b1 t1 a1 39 4
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b4:0 -
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v2 SP t19 0 - p0:0:0:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 1 -
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v2,v20,v12,v1
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
b b4 Plain p23:99:6:0:0 0 0 - - b3:0 b1:1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v2
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b4:0,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v2,v8
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v34,v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
fstate scheduled,laidout
dcllen 10
zvar v7:1
end
pass 52 "late nilcheck"
f b1 t1 a1 39 4
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b4:0 -
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v2 SP t19 0 - p0:0:0:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 1 -
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v2,v20,v12,v1
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
b b4 Plain p23:99:6:0:0 0 0 - - b3:0 b1:1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v2
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b4:0,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v2,v8
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v34,v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
fstate scheduled,laidout
dcllen 10
zvar v7:1
end
pass 53 "flagalloc"
f b1 t1 a1 39 4
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b4:0 -
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v2 SP t19 0 - p0:0:0:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 1 -
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v2,v20,v12,v1
v v13 ARM64MOVDaddr t20 0 a8 p0:0:0:0:0 1 v3
v v15 ARM64MOVDconst t7 1 - p0:0:0:0:0 1 -
v v14 ARM64MOVDconst t19 16 - p0:0:0:0:0 1 -
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v14,v13,v15,v39
v v18 SelectN t36 0 - p23:99:6:0:0 3 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
b b4 Plain p23:99:6:0:0 0 0 - - b3:0 b1:1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v4 ARM64MOVDaddr t36 0 a3 p0:0:0:0:0 1 v2
v v27 ARM64MOVDaddr t19 0 a8 p23:99:6:0:0 1 v3
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v27,v18,v4,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
b b3 Ret p23:100:2:1:0 0 0 - v28 - b4:0,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v21 ARM64MOVDaddr t20 0 a11 p0:0:0:0:0 1 v3
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v2,v8
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v21,v18,v7,v6,v5,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev v34,v9,v33,v25,v38,v35,v36,v31
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
fstate scheduled,laidout
dcllen 10
zvar v7:1
end
pass 54 "regalloc"
aux a1 call "AuxCall{fmt.Sscan}" a2 1 2 2 8 40 5 3
abiparam in 0 t2 a3 0,1 0
abiparam in 1 t3 a4 2,3,4 16
abiparam out 0 t5 a5 0 -1
abiparam out 1 t6 a6 1,2 -1
callreg 0:1,1:2,2:4 - 0 -
aux a9 call "AuxCall{runtime.mallocgcSmallScanNoHeaderSC2}" a10 1 3 1 8 24 3 1
abiparam in 0 t19 - 0 0
abiparam in 1 t20 - 1 8
abiparam in 2 t7 - 2 16
abiparam out 0 t36 - 0 -1
callreg 0:1,1:2,2:4 0:1 7fffffff97ffffff -
aux a23 call "AuxCall{runtime.wbMove}" a24 1 3 0 8 24 3 0
abiparam in 0 t19 - 0 0
abiparam in 1 t19 - 1 8
abiparam in 2 t19 - 2 16
callreg 0:1,1:2,2:4 - 7fffffff97ffffff -
aux a12 call "AuxCall{fmt.Fscan}" a13 1 2 2 8 40 5 3
abiparam in 0 t42 - 0,1 0
abiparam in 1 t3 - 2,3,4 16
abiparam out 0 t5 - 0 -1
abiparam out 1 t6 - 1,2 -1
callreg 0:1,1:2,2:4,3:8,4:10 0:1,1:2,2:4 7fffffff97ffffff -
f b1 t1 a1 47 4
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b4:0 -
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v35 StoreReg t5 0 - p23:100:2:2:0 1 v5
v v38 StoreReg t5 0 - p23:100:2:2:0 1 v6
v v25 StoreReg t45 0 - p23:100:2:2:0 1 v7
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v2 SP t19 0 - p0:0:0:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 1 -
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v2,v20,v12,v1
v v34 ARM64MOVDconst t19 16 - p23:99:6:2:0 1 -
v v9 ARM64MOVDaddr t20 0 a8 p23:99:6:2:0 1 v3
v v33 ARM64MOVDconst t7 1 - p23:99:6:2:0 1 -
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v34,v9,v33,v39
v v18 SelectN t36 0 - p23:99:6:0:0 4 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
b b4 Plain p23:99:6:0:0 0 0 - - b3:0 b1:1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v41 StoreReg t36 0 - p23:99:6:0:0 1 v18
v v36 Copy t36 0 - p23:99:6:2:0 1 v18
v v31 ARM64MOVDaddr t36 0 a3 p23:99:6:2:0 1 v2
v v40 ARM64MOVDaddr t19 0 a8 p23:99:6:2:0 1 v3
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v40,v36,v31,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
v v47 LoadReg t36 0 - p23:99:6:2:0 0 v41
b b3 Ret p23:100:2:1:0 0 0 - v28 - b4:0,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v2,v8
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v42 Copy t36 0 - p23:100:14:2:0 1 v18
v v43 LoadReg t45 0 - p23:100:14:2:0 1 v25
v v44 LoadReg t5 0 - p23:100:14:2:0 1 v38
v v45 LoadReg t5 0 - p23:100:14:2:0 1 v35
v v46 ARM64MOVDaddr t20 0 a11 p23:100:14:2:0 1 v3
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v46,v42,v43,v44,v45,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev -
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
fstate scheduled,laidout
regalloc 48 v2:SP,v3:SB,v5:R4,v6:R3,v7:R2,v9:R1,v11:R3,v12:R1,v16:[R0],v18:R0,v20:R0,v22:[],v23:[R0;R1;R2],v25:@a4/t45/0/-/0,v26:R0,v28:[],v29:R1,v30:R2,v31:R2,v32:F0,v33:R2,v34:R0,v35:@a4/t5/16/-/0,v36:R1,v38:@a4/t5/8/-/0,v40:R0,v41:@a14/t36/0/-/0,v42:R1,v43:R2,v44:R3,v45:R4,v46:R0,v47:R0
dcllen 10
zvar v7:1
end
pass 55 "loop rotate"
f b1 t1 a1 47 4
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b4:0 -
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v35 StoreReg t5 0 - p23:100:2:2:0 1 v5
v v38 StoreReg t5 0 - p23:100:2:2:0 1 v6
v v25 StoreReg t45 0 - p23:100:2:2:0 1 v7
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v2 SP t19 0 - p0:0:0:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 1 -
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v2,v20,v12,v1
v v34 ARM64MOVDconst t19 16 - p23:99:6:2:0 1 -
v v9 ARM64MOVDaddr t20 0 a8 p23:99:6:2:0 1 v3
v v33 ARM64MOVDconst t7 1 - p23:99:6:2:0 1 -
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v34,v9,v33,v39
v v18 SelectN t36 0 - p23:99:6:0:0 4 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
b b4 Plain p23:99:6:0:0 0 0 - - b3:0 b1:1
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v41 StoreReg t36 0 - p23:99:6:0:0 1 v18
v v36 Copy t36 0 - p23:99:6:2:0 1 v18
v v31 ARM64MOVDaddr t36 0 a3 p23:99:6:2:0 1 v2
v v40 ARM64MOVDaddr t19 0 a8 p23:99:6:2:0 1 v3
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v40,v36,v31,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
v v47 LoadReg t36 0 - p23:99:6:2:0 0 v41
b b3 Ret p23:100:2:1:0 0 0 - v28 - b4:0,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v2,v8
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v42 Copy t36 0 - p23:100:14:2:0 1 v18
v v43 LoadReg t45 0 - p23:100:14:2:0 1 v25
v v44 LoadReg t5 0 - p23:100:14:2:0 1 v38
v v45 LoadReg t5 0 - p23:100:14:2:0 1 v35
v v46 ARM64MOVDaddr t20 0 a11 p23:100:14:2:0 1 v3
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v46,v42,v43,v44,v45,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev -
freeb -
cache postorder b3,b2,b4,b1
cache idom b1:-,b4:b1,b2:b1,b3:b1
cache sdom b1:-:b4:-:2:23,b4:b1:-:b2:5:8,b2:b1:-:b3:11:14,b3:b1:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
fstate scheduled,laidout
regalloc 48 v2:SP,v3:SB,v5:R4,v6:R3,v7:R2,v9:R1,v11:R3,v12:R1,v16:[R0],v18:R0,v20:R0,v22:[],v23:[R0;R1;R2],v25:@a4/t45/0/-/0,v26:R0,v28:[],v29:R1,v30:R2,v31:R2,v32:F0,v33:R2,v34:R0,v35:@a4/t5/16/-/0,v36:R1,v38:@a4/t5/8/-/0,v40:R0,v41:@a14/t36/0/-/0,v42:R1,v43:R2,v44:R3,v45:R4,v46:R0,v47:R0
dcllen 10
zvar v7:1
end
pass 56 "trim"
f b1 t1 a1 47 4
b b1 ARM64NZW p23:99:6:0:0 -1 0 - v11 b2:0,b3:0 -
v v20 ArgIntReg t20 0 a15 p23:100:2:2:0 1 -
v v12 ArgIntReg t5 1 a16 p23:100:2:2:0 1 -
v v7 ArgIntReg t45 2 a17 p23:100:2:2:0 1 -
v v6 ArgIntReg t5 3 a18 p23:100:2:2:0 1 -
v v5 ArgIntReg t5 4 a19 p23:100:2:2:0 1 -
v v35 StoreReg t5 0 - p23:100:2:2:0 1 v5
v v38 StoreReg t5 0 - p23:100:2:2:0 1 v6
v v25 StoreReg t45 0 - p23:100:2:2:0 1 v7
v v3 SB t19 0 - p0:0:0:0:0 4 -
v v2 SP t19 0 - p0:0:0:0:0 3 -
v v1 InitMem t31 0 - p0:0:0:0:0 1 -
v v39 ARM64STP t31 0 a3 p23:99:6:1:0 1 v2,v20,v12,v1
v v34 ARM64MOVDconst t19 16 - p23:99:6:2:0 1 -
v v9 ARM64MOVDaddr t20 0 a8 p23:99:6:2:0 1 v3
v v33 ARM64MOVDconst t7 1 - p23:99:6:2:0 1 -
v v16 ARM64CALLstatic t39 40 a9 p23:99:6:0:0 2 v34,v9,v33,v39
v v18 SelectN t36 0 - p23:99:6:0:0 4 v16
v v17 SelectN t31 1 - p23:99:6:0:0 3 v16
v v11 ARM64MOVWUload t14 0 a22 p23:99:6:0:0 1 v3,v17
b b2 Plain p23:99:6:0:0 0 0 - - b3:1 b1:0
v v41 StoreReg t36 0 - p23:99:6:0:0 1 v18
v v36 Copy t36 0 - p23:99:6:2:0 1 v18
v v31 ARM64MOVDaddr t36 0 a3 p23:99:6:2:0 1 v2
v v40 ARM64MOVDaddr t19 0 a8 p23:99:6:2:0 1 v3
v v22 ARM64CALLstatic t35 24 a23 p23:99:6:0:0 1 v40,v36,v31,v17
v v10 SelectN t31 0 - p23:99:6:0:0 1 v22
v v47 LoadReg t36 0 - p23:99:6:2:0 0 v41
b b3 Ret p23:100:2:1:0 0 0 - v28 - b1:1,b2:0
v v8 Phi t31 0 - p23:99:6:2:0 2 v17,v10
v v32 ARM64FMOVQload t46 0 a3 p23:99:6:0:0 1 v2,v8
v v37 ARM64FMOVQstore t31 0 - p23:99:6:0:0 1 v18,v32,v8
v v19 WBend t31 0 - p23:99:6:2:0 1 v37
v v42 Copy t36 0 - p23:100:14:2:0 1 v18
v v43 LoadReg t45 0 - p23:100:14:2:0 1 v25
v v44 LoadReg t5 0 - p23:100:14:2:0 1 v38
v v45 LoadReg t5 0 - p23:100:14:2:0 1 v35
v v46 ARM64MOVDaddr t20 0 a11 p23:100:14:2:0 1 v3
v v23 ARM64CALLstatic t44 40 a12 p23:100:14:1:0 4 v46,v42,v43,v44,v45,v19
v v26 SelectN t5 0 - p23:100:14:1:0 1 v23
v v29 SelectN t19 1 - p23:100:14:1:0 1 v23
v v30 SelectN t20 2 - p23:100:14:2:0 1 v23
v v24 SelectN t31 3 - p23:100:14:0:0 1 v23
v v28 MakeResult t44 0 - p23:100:2:0:0 1 v26,v29,v30,v24
names s2,s3,s4,s5
named s2 v18
named s3 v7
named s4 v6
named s5 v5
splits s1/0/t45=s3,s1/8/t5=s4,s1/16/t5=s5
canon a4/t3/0/-/0=s1,a14/t36/0/-/0=s2
consts -
freev -
freeb -
cache auxmap -:1,a3:2,a4:3,a8:4,a11:5,a15:6,a16:7,a17:8,a18:9,a19:10,a22:11
cache linestarts 23:99:100
fstate scheduled,laidout
regalloc 48 v2:SP,v3:SB,v5:R4,v6:R3,v7:R2,v9:R1,v11:R3,v12:R1,v16:[R0],v18:R0,v20:R0,v22:[],v23:[R0;R1;R2],v25:@a4/t45/0/-/0,v26:R0,v28:[],v29:R1,v30:R2,v31:R2,v32:F0,v33:R2,v34:R0,v35:@a4/t5/16/-/0,v36:R1,v38:@a4/t5/8/-/0,v40:R0,v41:@a14/t36/0/-/0,v42:R1,v43:R2,v44:R3,v45:R4,v46:R0,v47:R0
dcllen 10
zvar v7:1
end
frontend
end
ptrcache t2,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t24,t27,t28,t29,t30,t36,t41
typelink t31=t35
typeorder t8,t12,t9,t13,t10,t14,t11,t15,t5,t18,t19,t28,t29,t16,t17,t7,t20,t21,t22,t23,t24,t25,t26,t27,t37,t45,t38,t36,t40,t1,t3,t4,t6,t42,t2,t41,t30,t31,t33,t32,t34,t46,t35,t39,t43,t44
eof
"#

/-- `std/std/fmt/Sscan,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "fmt"
func "Sscan" 1
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
name n1 "str" PPARAM t1 2 "fmt.str" 0 a3
type t2 24 8 8 1 01 "[]any"
name n2 "a" PPARAM t2 1 "fmt.a" 0 a4
type t3 8 8 0 0 - "int"
name n3 "n" PPARAMOUT t3 1 "fmt.n" 0 a5
type t4 16 8 16 1 02 "error"
name n4 "err" PPARAMOUT t4 1 "fmt.err" 0 a6
name n5 ".autotmp_4" PAUTO t3 1 "fmt..autotmp_4" 0 -
name n6 ".autotmp_5" PAUTO t4 1 "fmt..autotmp_5" 0 -
type t5 8 8 8 1 01 "*stringReader"
name n7 ".autotmp_6" PAUTO t5 3 "fmt..autotmp_6" 0 -
name n8 ".autotmp_7" PAUTO t3 3 "fmt..autotmp_7" 0 -
name n9 ".autotmp_8" PAUTO t4 3 "fmt..autotmp_8" 0 -
type t6 8 8 8 1 01 "*string"
name n10 "&str" PAUTO t6 0 "fmt.&str" 0 a14
in n1 0 used,addrtaken,heapaddr
in n2 16 used
in n3 0 outregs
in n4 0 outregs
in n5 0 used,autotmp
in n6 0 used,autotmp
in n7 0 used,autotmp
in n8 0 used,autotmp
in n9 0 used,autotmp
in n10 0 used
out n1 0 used,addrtaken,heapaddr
out n2 16 used
out n10 -8 used
opt n6 0 autotmp
opt n7 0 autotmp
opt n9 0 autotmp
opt n4 0 outregs
opt n5 0 autotmp
opt n8 0 autotmp
opt n3 0 outregs
stack 8 8 8
end
genin
posbase p23 "fmt/scan.go" 1 1 -1 21 "fmt/scan.go" "fmt/scan.go" 1 1
type t7 8 8 8 1 01 "*uint8"
sym y1 "fmt.Sscan" 1
curfn p23:99:6:0:0 0 0
regargs 8192:0:t7,8193:8:t3,8194:16:t7,8195:24:t3,8196:32:t3
text y1 0 0 0 0 99 200080
end
prog0
sym y2 "gclocals\xc2\xb7itaneJMpbAudh9zNu5JnHA==" 0
sym y3 "gclocals\xc2\xb7wOtHgd1PPo+5LvI/jNo6Ag==" 0
sym y4 "fmt.Sscan.arginfo1" 0
sym y5 "fmt.Sscan.argliveinfo" 0
sym y6 "fmt.a" 0
sym y7 "fmt.str" 0
sym y8 "type:string" 0
sym y9 "runtime.mallocgcSmallScanNoHeaderSC2" 1
sym y10 "runtime.writeBarrier" 0
sym y11 "fmt.&str" 0
sym y12 "runtime.wbMove" 1
sym y13 "go:itab.*fmt.stringReader,io.Reader" 0
sym y14 "fmt.Fscan" 1
sym y15 "type:*fmt.stringReader" 0
type t8 8 8 8 1 01 "*any"
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/48/-/i40 0 0 p23:99:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p23:99:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p23:99:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p23:99:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p23:99:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p23:99:6:2:0
p 6 6 0 0 0 - MOVD 0 REG/8196/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/PARAM/0/32/y6/- 0 0 p23:100:2:2:0
p 7 7 0 0 0 - MOVD 0 REG/8195/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/PARAM/0/24/y6/- 0 0 p23:100:2:2:0
p 8 8 0 0 0 - MOVD 0 REG/8194/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/PARAM/0/16/y6/- 0 0 p23:100:2:2:0
p 9 9 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p23:100:2:2:0
p 10 10 0 0 0 - STP 0 REGREG/8192/0/0/NONE/0/8193/-/- 0 - MEM/8383/0/0/PARAM/0/0/y7/- 0 0 p23:99:6:1:0
p 11 11 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/16/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p23:99:6:2:0
p 12 12 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/0/y8/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p23:99:6:2:0
p 13 13 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/1/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p23:99:6:2:0
p 14 14 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p23:99:6:2:0
p 15 15 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y9/- 0 0 p23:99:6:2:0
p 16 16 0 0 0 - MOVWU 0 MEM/0/0/0/EXTERN/0/0/y10/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p23:99:6:2:0
p 17 17 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p23:99:6:0:0
p 18 18 0 0 0 - CBZW 0 REG/8195/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@25 0 0 p23:99:6:2:0
p 19 19 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/AUTO/0/-8/y11/- 0 0 p23:99:6:2:0
p 20 20 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p23:99:6:2:0
p 21 21 0 0 0 - MOVD 0 ADDR/8383/0/0/PARAM/0/0/y7/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p23:99:6:2:0
p 22 22 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/0/y8/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p23:99:6:2:0
p 23 23 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y12/- 0 0 p23:99:6:2:0
p 24 24 0 0 0 - MOVD 0 MEM/8383/0/0/AUTO/0/-8/y11/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p23:99:6:2:0
p 25 25 0 0 0 - FMOVQ 0 MEM/8383/0/0/PARAM/0/0/y7/- 0 - REG/8224/0/0/NONE/0/0/-/- 0 0 p23:99:6:2:0
p 26 26 0 0 0 - FMOVQ 0 REG/8224/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 0 0 p23:99:6:2:0
p 27 27 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p23:100:14:2:0
p 28 28 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p23:100:14:1:0
p 29 29 0 0 0 - MOVD 0 MEM/8383/0/0/PARAM/0/16/y6/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p23:100:14:2:0
p 30 30 0 0 0 - MOVD 0 MEM/8383/0/0/PARAM/0/24/y6/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p23:100:14:2:0
p 31 31 0 0 0 - MOVD 0 MEM/8383/0/0/PARAM/0/32/y6/- 0 - REG/8196/0/0/NONE/0/0/-/- 0 0 p23:100:14:2:0
p 32 32 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/0/y13/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p23:100:14:2:0
p 33 33 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p23:100:14:1:0
p 34 34 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y14/- 0 0 p23:100:14:1:0
p 35 35 0 0 0 - RET 0 _ 0 - _ 0 0 p23:100:2:2:0
p 36 36 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 99 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 8195 STP LDP
spill MEM/8383/0/0/NONE/0/40/-/- 8196 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 1
reloc 0 0 R_USEIFACE 0 y15
symalign y2:4,y3:4,y4:1,y5:1,y13:8
autot -
dbgentry 1
dbgslot 0 n10 t6 0
dbgslot 1 n2 t8 0
dbgslot 2 n2 t3 8
dbgslot 3 n2 t3 16
dbgslot 4 n1 t7 0
dbgslot 5 n1 t3 8
dbgvar 0 n10 0
dbgvar 1 n2 1,2,3
dbgvar 2 n1 4,5
dbgloc 0 1:18:2:40:50,2:40:3:-10000:9170,3:-10000:3:46:50
dbgloc 1 1:-10000:1:33:529308539308549308,1:33:1:16:911893089120930891289308,1:16:-1:-30000:911893089120930891289308
dbgloc 2 1:-10000:1:34:509308519308,1:34:1:9:9308519308
dbgregout n3,n4
dbgpc 1:18:16,2:40:23,3:-10000:25,3:46:33,1:33:14,1:16:16,1:34:12,1:9:13
end
asm
sym y16 "runtime.morestack_noctxt" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
sym y21 "" 0
sym y22 "" 0
sym y23 "" 0
sym y24 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/64/-/i40 0 0 p23:99:6:0:0
p 37 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p23:99:6:0:0
p 38 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p23:99:6:0:0
p 39 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p23:99:6:0:0
p 40 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@51 0 0 p23:99:6:0:0
p 41 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p23:99:6:0:0
p 42 12 64 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-64/-/- 0 0 p23:99:6:0:1
p 43 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p23:99:6:0:0
p 44 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p23:99:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p23:99:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p23:99:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p23:99:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p23:99:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p23:99:6:2:0
p 6 24 0 0 304 - MOVD 0 REG/8196/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/32/y6/- 0 0 p23:100:2:2:0
p 7 28 0 0 304 - MOVD 0 REG/8195/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/47/24/y6/- 0 0 p23:100:2:2:0
p 8 32 0 0 304 - MOVD 0 REG/8194/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/16/y6/- 0 0 p23:100:2:2:0
p 9 36 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p23:100:2:2:0
p 10 36 0 0 428 - STP 0 REGREG/8192/0/0/NONE/7/8193/-/- 0 - MEM/0/0/0/PARAM/48/0/y7/- 0 0 p23:99:6:1:0
p 11 40 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/16/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p23:99:6:2:0
p 12 44 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/0/y8/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p23:99:6:2:0
p 13 52 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/1/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p23:99:6:2:0
p 14 56 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p23:99:6:2:0
p 15 56 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y9/- 0 0 p23:99:6:2:0
p 45 60 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-3/-/- 0 0 p23:99:6:2:0
p 16 60 0 0 397 - MOVWU 0 MEM/0/0/0/EXTERN/110/0/y10/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p23:99:6:2:0
p 46 68 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p23:99:6:2:0
p 17 68 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p23:99:6:0:0
p 18 68 0 0 85 - CBZW 0 REG/8195/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/25/-/@25 0 0 p23:99:6:2:0
p 19 72 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/AUTO/47/-8/y11/- 0 0 p23:99:6:2:0
p 20 76 0 0 301 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p23:99:6:2:0
p 21 80 0 0 325 - MOVD 0 ADDR/0/0/0/PARAM/32/0/y7/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p23:99:6:2:0
p 22 84 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/0/y8/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p23:99:6:2:0
p 23 92 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y12/- 0 0 p23:99:6:2:0
p 24 96 0 0 329 - MOVD 0 MEM/0/0/0/AUTO/47/-8/y11/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p23:99:6:2:0
p 25 100 0 0 176 - FMOVQ 0 MEM/0/0/0/PARAM/48/0/y7/- 0 - REG/8224/0/0/NONE/5/0/-/- 0 0 p23:99:6:2:0
p 26 104 0 0 169 - FMOVQ 0 REG/8224/0/0/NONE/5/0/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 0 0 p23:99:6:2:0
p 27 108 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p23:100:14:2:0
p 28 108 0 0 301 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p23:100:14:1:0
p 29 112 0 0 329 - MOVD 0 MEM/0/0/0/PARAM/48/16/y6/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p23:100:14:2:0
p 30 116 0 0 329 - MOVD 0 MEM/0/0/0/PARAM/47/24/y6/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p23:100:14:2:0
p 31 120 0 0 329 - MOVD 0 MEM/0/0/0/PARAM/48/32/y6/- 0 - REG/8196/0/0/NONE/2/0/-/- 0 0 p23:100:14:2:0
p 32 124 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/0/y13/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p23:100:14:2:0
p 33 132 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p23:100:14:1:0
p 34 132 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y14/- 0 0 p23:100:14:1:0
p 35 136 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p23:100:2:2:0
p 47 140 -64 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/64/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p23:100:2:2:0
p 48 144 64 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p23:100:2:2:0
p 49 148 -64 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p23:100:2:2:0
p 50 148 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p23:99:6:0:0
p 51 148 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p23:99:6:0:0
p 52 148 0 0 436 - STP 0 REGREG/8192/0/0/NONE/7/8193/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p23:99:6:0:0
p 53 152 0 0 436 - STP 0 REGREG/8194/0/0/NONE/7/8195/-/- 0 - MEM/8383/0/0/NONE/87/24/-/- 0 0 p23:99:6:0:0
p 54 156 0 0 308 - MOVD 0 REG/8196/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/40/-/- 0 0 p23:99:6:0:0
p 55 160 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p23:99:6:0:0
p 56 164 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y16/- 0 0 p23:99:6:0:0
p 57 168 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p23:99:6:0:0
p 58 168 0 0 245 - LDP 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REGREG/8192/0/0/NONE/7/8193/-/- 0 0 p23:99:6:0:0
p 59 172 0 0 245 - LDP 0 MEM/8383/0/0/NONE/87/24/-/- 0 - REGREG/8194/0/0/NONE/7/8195/-/- 0 0 p23:99:6:0:0
p 60 176 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/40/-/- 0 - REG/8196/0/0/NONE/2/0/-/- 0 0 p23:99:6:0:0
p 61 180 64 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@37 0 0 p23:99:6:0:0
fn y1 40 56 0 0 99 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 8195 STP LDP
spill MEM/8383/0/0/NONE/0/40/-/- 8196 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 192 0 900b40f9ff6330eb69040054fe0f1cf8fd831ff8fd2300d1e43700f9e33300f9e22f00f9e08704a9e0037cb20100009021000091e20340b2000000941b000090630340b903010034e01b00f9e10300aae2230191000000900000009100000094e01b40f9e083c43c0000803de10300aae22f40f9e33340f9e43740f9000000900000009100000094fd835ff8fe0744f8c0035fd6e08700a9e28f01a9e41700f9e3031eaa00000094e08740a9e28f41a9e41740f9d3ffff170000000000000000 9
reloc 0 0 R_USEIFACE 0 y15
reloc 44 8 R_ADDRARM64 0 y8
reloc 56 4 R_CALLARM64 0 y9
reloc 60 8 R_ARM64_PCREL_LDST32 0 y10
reloc 84 8 R_ADDRARM64 0 y8
reloc 92 4 R_CALLARM64 0 y12
reloc 124 8 R_ADDRARM64 0 y13
reloc 132 4 R_CALLARM64 0 y14
reloc 164 4 R_CALLARM64 0 y16
pcln y21 y22 y23 y24 y17,y18,y19,y20 y2,y3,_,_,_,y4,y5
usedfiles 21
data y2 Sxxx 0 4 8000 02000000030000000500 0
data y3 Sxxx 0 4 8000 02000000010000000000 0
data y4 SDATA 15 1 8000 fe00080808fdfe100818082008fdff 0
data y5 SDATA 2 1 8000 1000 0
data y17 SRODATA 17 1 28000 00010102020c0302020a020a0105020600 0
data y18 SRODATA 9 1 28000 000e02130204030b00 0
data y19 SRODATA 0 1 28000 - 0
data y20 SRODATA 7 1 28000 00060403032700 0
data y21 SRODATA 8 1 28000 02048001207f0c00 0
data y22 SRODATA 3 1 28000 2c3000 0
data y23 SRODATA 12 1 28000 c8010602030112020a010b00 0
data y24 SRODATA 3 1 28000 003000 0
end
dwarf
sym y25 "" 0
sym y26 "" 0
sym y27 "" 0
sym y28 "" 0
sym y29 "go:info.string" 0
sym y30 "go:info.[]interface {}" 0
sym y31 "go:info.int" 0
sym y32 "go:info.error" 0
sym y33 "go:info.*string" 0
sym y34 "type:error" 0
sym y35 "type:int" 0
dwfn y25 y26 y27 - y28 "fmt.Sscan" 21:99 1 0 1 254
dwdcl n1,n2,n10
dwclosure 0 -
dwparents -
dwparams n1,n2,n3,n4
dwname n1 1 1 0 0 0 0 0 0 n10 - "string" 0 0 1 p23:99:12:0:0
dwname n2 1 1 0 0 0 0 16 0 - - "[]interface {}" 0 0 1 p23:99:24:0:0
dwname n10 1 1 0 0 0 0 -8 0 - - "*string" 0 0 1 p23:99:12:0:0
dwname n6 1 0 1 0 0 0 0 0 - - "error" 0 0 1 p23:100:2:0:0
dwname n7 1 0 1 0 0 0 0 0 - - "*fmt.stringReader" 0 0 1 p23:100:30:0:0
dwname n9 1 0 1 0 0 0 0 0 - - "error" 0 0 1 p23:100:2:0:0
dwname n4 1 0 0 0 0 0 0 1 - - "error" 0 0 1 p23:99:42:0:0
dwname n5 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p23:100:2:0:0
dwname n8 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p23:100:2:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "int" 0 0 1 p23:99:35:0:0
var 0 0 "str" 5 1 0 0 0 8 y29 "fmt/scan.go" 99 12 0 0 0 0 v2
var 1 0 "a" 5 1 0 0 0 24 y30 "fmt/scan.go" 99 24 0 1 0 0 v1
var 2 0 "n" 5 1 1 0 0 0 y31 "fmt/scan.go" 99 35 0 2 0 0 -
var 3 0 "err" 5 1 1 0 0 0 y32 "fmt/scan.go" 99 42 0 3 0 0 -
var 4 0 "&str" 52 1 0 0 0 -16 y33 "fmt/scan.go" 99 12 0 4 0 0 v0
scope 0 0 - 0,1,2,3,4
data y25 SDWARFFCN 89 0 0 03666d742e537363616e000000c001019c1600000063012d73747200006300000000000000002d6100006300000000000000002e6e00016300000000002e657272000163000000000027267374720063000000000000000000 12
reloc 0 0 R_USETYPE 0 y15
reloc 0 0 R_USETYPE 0 y34
reloc 0 0 R_USETYPE 0 y35
reloc 11 2 R_DWTXTADDR_U2 0 y1
reloc 30 4 R_DWARFSECREF 0 y29
reloc 34 4 R_DWARFSECREF 0 y26
reloc 43 4 R_DWARFSECREF 0 y30
reloc 47 4 R_DWARFSECREF 23 y26
reloc 56 4 R_DWARFSECREF 0 y31
reloc 68 4 R_DWARFSECREF 0 y32
reloc 80 4 R_DWARFSECREF 0 y33
reloc 84 4 R_DWARFSECREF 73 y26
data y26 SDWARFLOC 94 0 0 01000004002c06509308519308042c34059308519308000100000400380952930853930854930804383c0c911893089120930891289308043cc0010c91189308912093089128930800010000043c5c0150045c6402917004648401015000 3
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 24 2 R_DWTXTADDR_U2 0 y1
reloc 74 2 R_DWTXTADDR_U2 0 y1
data y27 SDWARFRANGE 0 0 0 - 0
data y28 SDWARFLINES 42 0 0 0009020000000000000000041603dd00140a8706880686063706022df6063706d706370686022c000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded `Sscan` (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `Sscan`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context `checkG66` runs `checkG66L` on and the end-to-end checks take (`liveCtx`). -/
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

/-- The entry stores at the head of `ids` as long as they last, without stepping over the values
`entrySkip` takes (`storesFrom` before #553's change). -/
def storesFromNoSkip (lc : LocCtx) (g : G2In) : List ID → List (Int × Nat)
  | [] => []
  | id :: ids =>
    match (lc.ctx.f.value? id).bind (entryStore? lc g) with
    | some w => w :: storesFromNoSkip lc g ids
    | none => []

/-- `entryStoresOK` on `storesFromNoSkip`. -/
def entryStoresOKNoSkip (lc : LocCtx) (g : G2In) (k : Nat) : Bool :=
  let st := match lc.ctx.f.block? lc.ctx.f.entry with
    | some blk => storesFromNoSkip lc g (blk.values.toList.drop k)
    | none => []
  (pendWins lc g).all fun (o, n) => (List.range n).all fun j => inWins st (o + j)

/-- The value at `entryLen` of the entry block. -/
def first : Option Value :=
  (lc.ctx.f.block? lc.ctx.f.entry).bind fun blk =>
    (blk.values[entryLen lc]?).bind lc.ctx.f.value?

/-- What compiled evaluation checks: `checkG66` accepts `Sscan`; `entryStoresOK` holds at
`entryLen` and `entryStoresOKNoSkip` does not; a window is pending; the value at `entryLen` is a
spill that `entrySkip` takes. -/
def sFacts : Bool :=
  (checkG66 lc0 ps bs g).toBool && entryStoresOK lc g (entryLen lc) &&
    !entryStoresOKNoSkip lc g (entryLen lc) && !(pendWins lc g).isEmpty &&
    first.any fun v => v.op == .StoreReg && entrySkip lc v

theorem skip_facts : sFacts = true := by
  native_decide

/-- **Entry stores after a spill** (`storesFrom`'s step over `entrySkip`): `checkG66` accepts
`fmt.Sscan`, whose entry stores come after spills and values without code; `entryStoresOK` holds
at `entryLen`, the check without that step does not, a window is pending, and the value at
`entryLen` is a spill `entrySkip` takes. -/
theorem entrySkip_witness :
    (checkG66 lc0 ps bs g).toBool = true ∧ entryStoresOK lc g (entryLen lc) = true ∧
      entryStoresOKNoSkip lc g (entryLen lc) = false ∧ pendWins lc g ≠ [] ∧
      ∃ v, first = some v ∧ v.op = .StoreReg ∧ entrySkip lc v = true := by
  have h := skip_facts
  simp only [sFacts, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, ?_⟩
  cases hf : first with
  | none => rw [hf] at h5; cases h5
  | some v =>
    rw [hf] at h5
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h5
    exact ⟨v, rfl, h5.1, h5.2⟩

end GoFV.Proof.Witness.ObjEntrySkip
