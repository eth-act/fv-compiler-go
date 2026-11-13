import GoFV.Proof.Gen.G37
import GoFV.Proof.Witness.GenG13

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G37 of the genssa validator on `math/bits.Reverse`

`std/std/math/bits/Reverse,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`;
`math/bits/bits.go`):

```go
func Reverse(x uint) uint {
	if UintSize == 32 {
		return uint(Reverse32(uint32(x)))
	}
	return uint(Reverse64(uint64(x)))
}
```

Block `b1` (the entry): `v6 = ArgIntReg` (`x`, `R0`), `InitMem`, `v9 = RBIT v6` (`RBIT R0, R0`:
the bits of `x` in reverse order), `MakeResult`. G36 has no bit reversal, so `checkG36` rejects the
function (`op RBIT`); `checkG37` accepts it with the PC table `tab` and the class table `kt`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g37_facts`),
`stepLoc` runs `v9` from a state with `x = 0x0f` in `R0` to `R0 = 0xf000000000000000`. On a framed
activation with `G28Env`, `g37_value` runs `RBIT R0, R0` (`genG37_witness`): the machine's `X0` is
`0xf000000000000000`.
-/

namespace GoFV.Proof.Witness.GenG37

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/math/bits/Reverse,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "math/bits"
func "Reverse" 1 0 0
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
config localpkg "math/bits"
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
type t2 UINT 8 8 0 comparable,named "uint" "uint"
type t1 FUNC 8 8 8 hasptr,direct "func(uint) uint" "func(uint) uint" 0 1 1
field 0 "x" t2 ? 0
field 1 "" t2 ? 0
aux a2 sym "math/bits.Reverse" "math/bits.Reverse" 1 - 0 - - - - 0
posbase p2 "math/bits/bits.go" 1 1 -1
aux a3 name "x" "x" PPARAM t2 0 1 used p2:226:14:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t2 0 1 - p2:226:22:0:0
aux a1 call "AuxCall{math/bits.Reverse}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
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
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t12
type t21 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t15
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
type t33 PTR 8 8 8 hasptr,direct,comparable "*uint" "*uint" t2
type t34 RESULTS ? ? ? - "uint,mem" "" 2 t2,t28
slot s1 a3 t2 0 - 0
f b1 t1 a1 11 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t14,UInt=t2,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Copy t11 0 - p2:230:31:2:0 1 v6
v v9 BitRev64 t11 0 - p2:230:23:0:0 1 v8
v v10 Copy t2 0 - p2:230:23:2:0 1 v9
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Copy t11 0 - p2:230:31:2:0 1 v6
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v8
v v10 Copy t2 0 - p2:230:23:2:0 1 v9
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:230:230
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:226:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Copy t11 0 - p2:230:31:2:0 0 v6
v v9 BitRev64 t11 0 - p2:230:23:1:0 2 v6
v v10 Copy t2 0 - p2:230:23:2:0 0 v9
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:230:230
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:230:230
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:230:230
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:230:230
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:230:230
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:230:230
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:230:230
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:230:230
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:226:6:2:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 20 "expand calls"
aux a5 nameoff "x+0" a3 0
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v8 SP t15 0 - p0:0:0:0:0 2 -
v v7 OffPtr t33 0 - p0:0:0:0:0 0 v8
v v5 LocalAddr t33 0 a4 p2:230:2:0:0 0 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 21 "decompose builtin"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v8 SP t15 0 - p0:0:0:0:0 2 -
v v7 OffPtr t33 0 - p0:0:0:0:0 0 v8
v v5 LocalAddr t33 0 a4 p2:230:2:0:0 0 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v8 SP t15 0 - p0:0:0:0:0 2 -
v v7 OffPtr t33 0 - p0:0:0:0:0 0 v8
v v5 LocalAddr t33 0 a4 p2:230:2:0:0 0 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v8 SP t15 0 - p0:0:0:0:0 2 -
v v7 OffPtr t33 0 - p0:0:0:0:0 0 v8
v v5 LocalAddr t33 0 a4 p2:230:2:0:0 0 v8,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 BitRev64 t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 33 "lower"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 36 "pair"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:230:230
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v5,v7,v8,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a1 call "AuxCall{math/bits.Reverse}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v8,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
fstate scheduled,laidout
regalloc 12 v6:R0,v9:R0,v11:[]
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v8,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
fstate scheduled,laidout
regalloc 12 v6:R0,v9:R0,v11:[]
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 11 1
b b1 Ret p2:230:23:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p2:230:23:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64RBIT t11 0 - p2:230:23:1:0 1 v6
v v11 MakeResult t34 0 - p2:230:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v8,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:230:230
fstate scheduled,laidout
regalloc 12 v6:R0,v9:R0,v11:[]
dcllen 3
end
frontend
end
ptrcache t5,t6,t7,t8,t10,t12,t13,t14,t15,t16,t17,t24
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t12,t2,t15,t25,t26,t13,t14,t3,t17,t18,t19,t20,t33,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t34
eof
"#

/-- `std/std/math/bits/Reverse,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "math/bits"
func "Reverse" 1
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
type t1 8 8 0 0 - "uint"
name n1 "x" PPARAM t1 1 "math/bits.x" 0 a3
name n2 "~r0" PPARAMOUT t1 1 "math/bits.~r0" 0 a4
type t2 8 8 0 0 - "uint64"
name n3 ".autotmp_2" PAUTO t2 3 "math/bits..autotmp_2" 0 -
in n1 0 used
in n2 0 outregs
in n3 0 used,autotmp
out n1 0 used
opt n3 0 autotmp
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p2 "math/bits/bits.go" 1 1 -1 1 "math/bits/bits.go" "math/bits/bits.go" 1 1
sym y1 "math/bits.Reverse" 1
curfn p2:226:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 226 200080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "math/bits.Reverse.arginfo1" 0
sym y4 "math/bits.Reverse.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:226:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:226:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:226:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:226:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:226:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:226:6:2:0
p 6 6 0 0 0 - RBIT 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:230:23:1:0
p 7 7 0 0 0 - RET 0 _ 0 - _ 0 0 p2:230:23:2:0
p 8 8 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 226 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:1:9:50
dbgregout n2
dbgpc 1:9:7
end
asm
sym y5 "" 0
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p2:226:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:226:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:226:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:226:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:226:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:226:6:2:0
p 6 0 0 0 91 - RBIT 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:230:23:1:0
p 7 4 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:230:23:2:0
fn y1 8 0 0 0 226 2000c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 16 0 0000c0dac0035fd60000000000000000 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 0 1 28000 - 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040400 0
data y9 SRODATA 3 1 28000 020400 0
data y10 SRODATA 3 1 28000 040400 0
data y11 SRODATA 4 1 28000 ce030400 0
data y12 SRODATA 3 1 28000 000400 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.uint" 0
sym y18 "type:uint" 0
dwfn y13 y14 y15 - y16 "math/bits.Reverse" 1:226 1 0 1 50
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "uint" 0 0 1 p2:226:14:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "uint64" 0 0 1 p2:230:23:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uint" 0 0 1 p2:226:22:0:0
var 0 0 "x" 5 1 0 0 0 8 y17 "math/bits/bits.go" 226 14 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y17 "math/bits/bits.go" 226 22 0 1 0 0 -
scope 0 0 - 0,1
data y13 SDWARFFCN 58 0 0 036d6174682f626974732e52657665727365000010019c02000000e201012d780000e20100000000000000002e7e72300001e201000000000000 5
reloc 0 0 R_USETYPE 0 y18
reloc 19 1 R_DWTXTADDR_U1 0 y1
reloc 36 4 R_DWARFSECREF 0 y17
reloc 40 4 R_DWARFSECREF 0 y14
reloc 52 4 R_DWARFSECREF 0 y17
data y14 SDWARFLOC 8 0 0 0100040004015000 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y16 SDWARFLINES 24 0 0 0009020000000000000000040203e001140637020c000101 1
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

/-- The PC table `checkG37` gives (`b1`: one entry per value `v6`, `v1`, `v9`, `v11`, then the
`RET`). -/
def tab : PcTab := [(1, [5, 5, 5, 7, 7])]

/-- The class table `checkG37` gives. -/
def kt : KTab := (match checkG37 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG37`. -/
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

/-- The `runLoc` state before `v9`: `x = 0x0f` (`v6`) in `R0`, every other register `poison`, the
empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w64 0x0f else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v9`: `X0 = 0x0f`, the activation's `g` and `FP`, the PC of `v9`, a zero
memory. -/
def m0 : MState :=
  { x := fun k => if k = 0 then 0x0f else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := fun _ => 0 }

/-- The register holds the 64-bit integer `0xf000000000000000`. -/
def isW64 : Option Val → Bool
  | some (.int .w64 x) => x == 0xf000000000000000
  | _ => false

theorem isW64_spec {o : Option Val} (h : isW64 o = true) :
    o = some (.int .w64 0xf000000000000000) := by
  unfold isW64 at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on `Reverse`: it holds an arm64 op, `checkG37` accepts it with
`tab` and `kt` and `checkG36` does not; it accesses no frame variable and has no home slot; `b1` is
the entry and holds `v9` (`RBIT v6`) at index 2, where `R0` has class 64 and G35's table is empty;
`stepLoc` runs `v9` from `s0` to `R0 = 0xf000000000000000`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG37 lc ps bs g).toOption == some (tab, kt) && (checkG36 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 9).isSome && blk.values[2]? == some 9 &&
    (val 9).op == .ARM64RBIT && (kAt lc kt 1 blk 2).get 0 == some 64 &&
    uL35 lc (uIn35 lc 1) blk 2 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 9)) fun s1 => isW64 s1.regs[0]?

theorem g37_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG37 lc ps bs g = .ok (tab, kt) ∧
      (checkG36 lc ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 9 = some (val 9) ∧ blk.values[2]? = some 9 ∧
      (val 9).op = .ARM64RBIT ∧ (kAt lc kt 1 blk 2).get 0 = some 64 ∧
      uL35 lc (uIn35 lc 1) blk 2 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 9)) (fun s1 => isW64 s1.regs[0]?) = true := by
  have hf := g37_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h36, hav, hsl, hm1, hbs, hvs, hi2, hop, hk0, hu2, hrun⟩ := hf
  refine ⟨hl, ?_, h36, hav, hsl, hm1, ?_, ?_, hi2, hop, hk0, hu2, hrun⟩
  · revert hres; cases checkG37 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g37Env (hc : checkG37 lc ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ := checkG37_spec hl hc
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ := checkG37_spec hl hc
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

/-! ## `v9`: `RBIT R0, R0` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w64 0x0f) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 2 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl (show m0.x 0 = 0x0f by decide)
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g37Inv0 (h0 : (kAt lc kt 1 blk 2).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk 2) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v9`, `RBIT`: none apply. -/
theorem pre9 {s : LocState} (hop : (val 9).op = .ARM64RBIT) : G14Pre lc s (val 9) := by
  have hne : ∀ o : Op, o ≠ .ARM64RBIT → (val 9).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G37 on `math/bits.Reverse`**: from the state with `x = 0x0f` in `R0`, `g37_value` runs
`v9 = RBIT v6` (`RBIT R0, R0`): `runLoc`'s `R0` holds `0xf000000000000000`, and the machine state,
related to it before `v11` under an activation extending `E` that is again a `G28Env`, has
`X0 = 0xf000000000000000`. `checkG36` rejects the function. -/
theorem genG37_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 9) = .ok s1 ∧
      s1.regs[0]? = some (.int .w64 0xf000000000000000) ∧
      (checkG36 lc ps bs g).toOption = none ∧
      E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E1 s1 1 3 m1 ∧ m1.x 0 = 0xf000000000000000 := by
  obtain ⟨hl, hc, h36, hav, hsl, hm1, hb, hv9, hi2, hop, hk0, hu2, hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr0 := isW64_spec hr
  have hE := g37Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64RBIT → (val 9).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g37_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm1 hb hi2 hv9 (by rw [hop]; rfl) locMatch0 (g37Inv0 hk0)
    (by rw [hu2]; intro e he; cases he) (pre9 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  have hx0 : m1.x 0 = 0xf000000000000000 := valRel_i64 hA ((hm1'.regs 0 _ hr0).1 0 rfl)
  exact ⟨s1, E1, m1, hs1, hr0, h36, hx1, hE1, hp1, hm1', hx0⟩

end GoFV.Proof.Witness.GenG37
