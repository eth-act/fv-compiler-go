import GoFV.Proof.Gen.G62
import GoFV.Proof.Witness.GenG14
import GoFV.Asm.ConstLoad

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G62 of the genssa validator on `runtime.syscall_Exit`'s ABI0 wrapper

`std/std/runtime/syscall_Exit,0.ssa` and `…,0.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`), loaded on P0'
(`p0PrimeSyms`, as `gen-check` runs G56 to G62): the `ABI0` wrapper of

```go
//go:linkname syscall_Exit syscall.Exit
func syscall_Exit(code int)
```

whose parameter `code` the `ABI0` ABI assigns to the stack (`abiparam in 0 … - 8`: no register).
Block `b1` (the entry) holds `v5 = Arg {code}` (homed in the slot of `code`, `NAME_PARAM` 0), then
`InitMem`, `v2 = LoadReg v5` (`MOVD code+0(FP), R0`) and the call of the `ABIInternal`
`syscall.Exit`. G61 has no `Arg` (`frame variable off another base`, `stack slot`), so `checkG61`
rejects the function; `checkG62` accepts it with the PC table `tab` and the class table `kt`. The
function needs no G48 mode (`needs48 lc = false`).

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g62_facts`),
`stepLoc` runs `v5` from the first state of an activation on `code = 7` (`s0`: its image the
8 bytes of 7, every register `poison`, no slot) to the slot of `code` holding 7. On a framed
activation with `G49Env` (the slot at `SP + 24`, where the machine `m0` holds the word 7: the
caller's stack argument, `ArgOK`; not G48's mode, `outSP = false`), `g62_value` at the mode
`false` relates that step to the machine, which runs no code (`genG62_witness`): the machine's word
at `SP + 24` is 7.
-/

namespace GoFV.Proof.Witness.GenG62

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/syscall_Exit,0.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "syscall_Exit" 0 1 0
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
config abiself 0
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
type t2 INT 8 8 0 comparable,named "int" "int"
type t1 FUNC 8 8 8 hasptr,direct "func(int)" "func(int)" 0 1 0
field 0 "code" t2 ? 0
aux a2 sym "syscall.Exit" "syscall.Exit" 0 - 0 - - - - 0
posbase p4 "runtime/runtime.go" 1 1 -1
aux a3 name "code" "code" PPARAM t2 0 1 used p4:132:19:0:0
aux a1 call "AuxCall{syscall.Exit}" a2 0 1 0 16 0 0 0
abiparam in 0 t2 a3 - 8
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t4 INT8 1 1 0 comparable,named "int8" "int8"
type t5 INT16 2 2 0 comparable,named "int16" "int16"
type t6 INT32 4 4 0 comparable,named "int32" "int32"
type t7 INT64 8 8 0 comparable,named "int64" "int64"
type t8 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t9 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t10 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t11 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t12 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t13 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t2
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
posbase p1 "<autogenerated>" 1 1 -1
aux a5 sym "syscall.Exit" "syscall.Exit" 1 - 0 - - - - 0
aux a4 call "AuxCall{syscall.Exit}" a5 1 1 0 8 8 1 0
abiparam in 0 t2 - 0 0
slot s1 a3 t2 0 - 0
f b1 t1 a1 8 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t2,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:0:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
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
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 3 "early deadcode"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 4 "short circuit"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 5 "decompose user"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 7 "opt"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 8 "zero arg cse"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 9 "opt deadcode"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 10 "generic cse"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 11 "phiopt"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 12 "gcse deadcode"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 13 "nilcheckelim"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 14 "prove"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 15 "divisible"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 16 "divmod"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 17 "middle opt"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 18 "known bits"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 19 "early fuse"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 20 "expand calls"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v4 SB t15 0 - p0:0:0:0:0 0 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v2 OffPtr t20 0 - p0:0:0:0:0 0 v3
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
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 21 "decompose builtin"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v4 SB t15 0 - p0:0:0:0:0 0 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v2 OffPtr t20 0 - p0:0:0:0:0 0 v3
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
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 22 "softfloat"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v4 SB t15 0 - p0:0:0:0:0 0 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v2 OffPtr t20 0 - p0:0:0:0:0 0 v3
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
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 23 "branchelim"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v4 SB t15 0 - p0:0:0:0:0 0 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v2 OffPtr t20 0 - p0:0:0:0:0 0 v3
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
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 24 "late opt"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 25 "dead auto elim"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 26 "sccp"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 27 "generic deadcode"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 28 "late fuse"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 29 "check bce"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 30 "dse"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 31 "memcombine"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 32 "writebarrier"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 33 "lower"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 34 "addressing modes"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 35 "late lower"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 36 "pair"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 38 "lowered cse"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 39 "elim unread autos"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 41 "lowered deadcode"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 42 "checkLower"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 43 "loop invariant"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 45 "tighten"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 46 "late deadcode"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 47 "critical"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 48 "phi tighten"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 49 "likelyadjust"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 50 "layout"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1
cache linestarts 1:1:1
fstate laidout
dcllen 1
end
pass 51 "schedule"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 1
end
pass 52 "late nilcheck"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 1
end
pass 53 "flagalloc"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 1
end
pass 54 "regalloc"
aux a4 call "AuxCall{syscall.Exit}" a5 1 1 0 8 8 1 0
abiparam in 0 t2 - 0 0
callreg 0:1 - 7fffffff97ffffff -
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 LoadReg t2 0 - p1:1:0:2:0 1 v5
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v2,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 7 v2:R0,v5:@a3/t2/0/-/0,v6:[]
dcllen 1
end
pass 55 "loop rotate"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 LoadReg t2 0 - p1:1:0:2:0 1 v5
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v2,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 7 v2:R0,v5:@a3/t2/0/-/0,v6:[]
dcllen 1
end
pass 56 "trim"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 LoadReg t2 0 - p1:1:0:2:0 1 v5
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v2,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 7 v2:R0,v5:@a3/t2/0/-/0,v6:[]
dcllen 1
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t21,t24,t25,t26,t27
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t2,t14,t15,t25,t26,t12,t13,t3,t17,t18,t19,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32
eof
"#

/-- `std/std/runtime/syscall_Exit,0.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "syscall_Exit" 0
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
type t1 8 8 0 0 - "int"
name n1 "code" PPARAM t1 1 "runtime.code" 0 a3
in n1 0 used
out n1 0 used
stack 0 0 8
end
genin
posbase p1 "<autogenerated>" 1 1 -1 0 "<autogenerated>" "<autogenerated>" 1 1
sym y1 "syscall.Exit" 0
curfn p1:1:0:0:0 0 0
regargs -
text y1 0 0 23 0 1 90085
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "syscall.Exit.arginfo0" 0
sym y4 "runtime.code" 0
sym y5 "syscall.Exit" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p1:1:0:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p1:1:0:0:0
p 4 4 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p1:1:0:2:0
p 5 5 0 0 0 - MOVD 0 MEM/8383/0/0/PARAM/0/0/y4/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p1:1:0:1:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p1:1:0:1:0
p 7 7 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p1:1:0:1:0
p 8 8 0 0 0 - RET 0 _ 0 - _ 0 0 p1:1:0:0:0
p 9 9 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 23 0 1 90085
funcaux y2 y2 - - y3 - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:-1:-30000:9108
dbgregout -
dbgpc -
end
asm
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i8 0 0 p1:1:0:0:0
p 10 0 32 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-32/-/- 0 0 p1:1:0:0:1
p 11 4 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p1:1:0:0:0
p 12 8 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 1 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p1:1:0:0:0
p 2 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p1:1:0:0:0
p 3 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p1:1:0:0:0
p 4 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:2:0
p 5 12 0 0 329 - MOVD 0 MEM/0/0/0/PARAM/48/0/y4/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p1:1:0:1:0
p 6 16 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p1:1:0:1:0
p 7 16 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y5/- 0 0 p1:1:0:1:0
p 8 20 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 13 24 -32 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/32/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 14 28 32 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p1:1:0:0:0
fn y1 8 24 23 0 1 90085
funcaux y2 y2 - - y3 - -
text 32 0 fe0f1ef8fd831ff8fd2300d1e01740f900000094fd835ff8fe0742f8c0035fd6 1
reloc 16 4 R_CALLARM64 0 y5
pcln y8 y9 y10 y11 y6,y7 y2,y2,_,_,_,y3
usedfiles 0
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y6 SRODATA 5 1 28000 0003010500 0
data y7 SRODATA 5 1 28000 0004020400 0
data y8 SRODATA 7 1 28000 020140063f0100 0
data y9 SRODATA 3 1 28000 020800 0
data y10 SRODATA 3 1 28000 040800 0
data y11 SRODATA 3 1 28000 000800 0
end
dwarf
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
posbase p4 "runtime/runtime.go" 1 1 -1 3 "runtime/runtime.go" "runtime/runtime.go" 1 1
sym y16 "go:info.int" 0
dwfn y12 y13 y14 - y15 "syscall.Exit" 0:1 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwname n1 1 1 0 0 0 0 0 0 - - "int" 0 0 1 p4:132:19:0:0
var 0 0 "code" 5 1 0 0 0 8 y16 "runtime/runtime.go" 132 19 0 0 0 0 v0
scope 0 0 - 0
data y12 SDWARFFCN 43 0 0 0373797363616c6c2e4578697400000020019c0100000001012d636f646500008401000000000000000000 3
reloc 14 2 R_DWTXTADDR_U2 0 y1
reloc 34 4 R_DWARFSECREF 0 y16
reloc 38 4 R_DWARFSECREF 0 y13
data y13 SDWARFLOC 10 0 0 01000004002002910800 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y14 SDWARFRANGE 0 0 0 - 0
data y15 SDWARFLINES 18 0 0 00090200000000000000000a0f0220000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`) with P0' (`p0PrimeSyms`, as `gen-check`
runs G56 to G62). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) := do
  let (lc, ps, bs, g) ← GenG2.load fSsa fProg
  let (syms', ps') ← GoFV.Asm.p0PrimeSyms g.syms ps
  return (lc, ps', bs, { g with syms := syms' })

/-- `runLoc`'s context of `syscall_Exit`'s wrapper. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G62's check runs on (`liveCtx`). -/
def lc : LocCtx := liveCtx lc0

/-- P0'. -/
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

/-- The PC table `checkG62` gives. -/
def tab : PcTab := (match checkG62 lc0 ps bs g with
  | .ok (t, _) => t
  | .error _ => [])

/-- The class table `checkG62` gives. -/
def kt : KTab := (match checkG62 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

/-- `b1`, the entry, whose value 0 is `v5 = Arg {code}`. -/
def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0''s layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame with 8 bytes of extra
space, every symbol at `symA`; `NAME_PARAM` 0 is `SP + 24`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, the home slots at their frame operands and the PC table of `checkG62`; not G48's mode
(`outSP = false`). -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := GenG2.sp0,
    slot := fun k => if k ∈ homeSlots lc then (g.slotOp k).map (fun p => frameOff L p.1 p.2) else none,
    g := 0x9000, lr := 0, fp := 0, framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The little-endian bytes of the word 7: the image of `code = 7`. -/
def img7 : Array Byte := #[.b 7, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0]

/-- The first `runLoc` state of an activation on `code = 7` (`runCtxLoc`'s, with the empty
memory): the image of `code`, every register `poison`, no slot. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 9 none, args := [.int .w64 7], mem0 := GenG2.mem0,
            images := #[img7] },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The caller's stack: the word 7 at `SP + 24` (`code+0(FP)`), 0 elsewhere. -/
def mem7 : Memory := fun a => if a = GenG2.sp0 + 24 then 7 else 0

/-- The machine before `v5`: the activation's `g` and `FP`, the PC of `v5`, the caller's stack
argument in memory. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 0, mem := mem7 }

/-- The home slots lie above the saved `LR` and below `2^64`. -/
def slotsFit : Bool :=
  (homeSlots lc).all fun k =>
    match g.slotOp k with
    | some (nc, off) => decide (8 ≤ frameOff L nc off) &&
        decide (GenG2.sp0.toNat + (frameOff L nc off).toNat + 8 ≤ 2 ^ 64)
    | none => true

/-- An `Arg` of aux `ax` and home `h`: its slot at `SP + 24` (`slot`) of 8 bytes (`size`), and
the read `rd` of its parameter's piece gives 7 at the shape `ty`. Generic in its inputs, so that
its spec never makes the kernel evaluate the function. -/
def argFactsAt (ax : Option AuxRef) (h : Option Location) (slot : SlotKey → Option Int)
    (size : SlotKey → Nat) (rd : AuxRef → Res Val) (ty : Ty) : Bool :=
  match ax, h with
  | some x, some (.slot k) =>
    slot k == some 24 && size k == 8 &&
      match rd x with
      | .ok y => (match y.retypeL ty with
        | .int .w64 n => n == 7
        | _ => false)
      | _ => false
  | _, _ => false

theorem argFactsAt_spec {ax : Option AuxRef} {h : Option Location} {slot : SlotKey → Option Int}
    {size : SlotKey → Nat} {rd : AuxRef → Res Val} {ty : Ty}
    (H : argFactsAt ax h slot size rd ty = true) :
    ∃ x k y, ax = some x ∧ h = some (.slot k) ∧ slot k = some 24 ∧ size k = 8 ∧
      rd x = .ok y ∧ y.retypeL ty = .int .w64 7 := by
  unfold argFactsAt at H
  split at H
  · rename_i x k
    simp only [Bool.and_eq_true, beq_iff_eq] at H
    obtain ⟨⟨h24, h8⟩, H⟩ := H
    split at H
    · rename_i y hy
      split at H
      · rename_i n hn
        simp only [beq_iff_eq] at H
        subst H
        exact ⟨x, k, y, rfl, rfl, h24, h8, hy, hn⟩
      · cases H
    · cases H
  · cases H

/-- `v5`'s slot is at `SP + 24`, holds 8 bytes, and `argVal` reads 7 for it from `s0`. -/
def argFacts : Bool :=
  argFactsAt (val 5).aux (lc.home 5) E.slot (fun k => (E.lc.slotTy k).size)
    (fun x => argVal lc.ctx s0.fr x (val 5).auxInt.toInt (lc.ty 5)) (lc.ty 5)

/-- After `v5`: the slot of `code` (home `h`) holds 7. -/
def holds7 (h : Option Location) (s : LocState) : Bool :=
  match h with
  | some (.slot k) =>
    match s.slots.lookup k with
    | some (.int .w64 n) => n == 7
    | _ => false
  | _ => false

theorem holds7_spec {h : Option Location} {s : LocState} (H : holds7 h s = true) :
    ∃ k, h = some (.slot k) ∧ s.slots.lookup k = some (.int .w64 7) := by
  unfold holds7 at H
  split at H
  · rename_i k
    split at H
    · rename_i n hn
      simp only [beq_iff_eq] at H
      subst H
      exact ⟨k, rfl, hn⟩
    · cases H
  · cases H

/-- What compiled evaluation checks on `syscall_Exit`'s wrapper: it holds an arm64 op; on P0',
`checkG62` accepts it with `tab` and `kt` and `checkG61` does not (G61 has no `Arg`); it accesses
no frame variable, its home slots fit and it needs no G48 mode; G2's symbols have no float
constant; `b1` holds `v5` (`Arg {code}`) at index 0, where G35's table is empty; `argFacts`;
`stepLoc` runs `v5` from `s0` to the slot of `code` holding 7, and `Ptr.ofAddr` reads 7 as no
block's address. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG62 lc0 ps bs g).toOption == some (tab, kt) && (checkG61 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && slotsFit && needs48 lc == false &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 5).isSome && blk.values[0]? == some 5 &&
    (val 5).op == .Arg && (val 5).id == 5 &&
    (constRo (symNames g)).isEmpty &&
    uL35 lc (uIn35 lc 1) blk 0 == [] && argFacts &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 5)) (holds7 (lc.home 5)) &&
    (Ptr.ofAddr 7).blk == .nil

theorem g62_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG62 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG61 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ slotsFit = true ∧ needs48 lc = false ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 5 = some (val 5) ∧ blk.values[0]? = some 5 ∧
      (val 5).op = .Arg ∧ (val 5).id = 5 ∧
      (constRo (symNames g)).isEmpty = true ∧
      uL35 lc (uIn35 lc 1) blk 0 = [] ∧ argFacts = true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 5)) (holds7 (lc.home 5)) = true ∧
      (Ptr.ofAddr 7).blk = .nil := by
  have hf := g62_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h61, hav, hfit, h48, hm1, hbs, hvs, hi0, hop, hid, hro, hu0, harg, hrun,
    h7⟩ := hf
  refine ⟨hl, ?_, h61, hav, hfit, h48, hm1, ?_, ?_, hi0, hop, hid, hro, hu0, harg, hrun, h7⟩
  · revert hres; cases checkG62 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g62Env (hc : checkG62 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
    (hav : (accessedVars lc).isEmpty = true) (hfit : slotsFit = true) :
    G49Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
            link := rfl
            pcOf := rfl
            retOut := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -, -, -⟩ :=
                checkG62L_spec hl (checkG62_spec hc).2
              intro p hp
              exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := GenG2.addrAgree
            glob := fun _ _ _ _ => rfl
            syms := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -, -, -⟩ :=
                checkG62L_spec hl (checkG62_spec hc).2
              intro y
              have hs : L.sym y = GenG2.symA := rfl
              rw [hs]
              refine ⟨by decide, fun p hp => ?_⟩
              exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
            calls := fun h => by cases h
            slot := fun k hk nc off hs => by simp [E, hk, hs]
            extra := by show 0 ≤ (8 : Int); decide
            frame := by
              refine ⟨by show 4096 + 8 ≤ GenG2.sp0.toNat; decide,
                by show GenG2.sp0.toNat + 8 ≤ 2 ^ 64; decide, fun k off hk => ?_⟩
              simp only [E] at hk
              split at hk
              · rename_i hmem
                obtain ⟨⟨nc, o⟩, hso, rfl⟩ := Option.map_eq_some_iff.1 hk
                have := List.all_eq_true.1 hfit k hmem
                simp only [hso, Bool.and_eq_true, decide_eq_true_eq] at this
                exact this
              · cases hk }
          vars := by
            intro x hx
            simp [List.isEmpty_iff.1 hav] at hx }
        wbs := fun h => by cases h }
      icalls := fun h => by cases h }
    memeqs := fun h => by cases h }
  vars := by
    intro x hx
    simp [List.isEmpty_iff.1 hav] at hx

/-! ## The state -/

/-- G2's symbols have no float constant: `RoPre56` holds at `s0`. -/
theorem ro0 (hro : (constRo (symNames g)).isEmpty = true) : RoPre56 g s0 := by
  intro mm _
  rw [List.isEmpty_iff.1 hro]
  intro n a h
  cases h

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) : x = .poison := by
  simp only [s0, Array.getElem?_replicate] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 0 m0 where
  regs := by
    intro r v hv
    rw [s0_regs hv]
    exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl,
    by simp only [MState.word, readMem, m0, mem7, E]; decide,
    by simp only [MState.word, readMem, m0, mem7, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g62Inv0 : G3Inv E lc (kAt lc kt 1 blk 0) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, GenG2.keys0, GenG2.sep0⟩
    rw [s0_regs hv]
    trivial
  slots := by intro k v h; simp [s0] at h

/-! ## `v5`: `Arg {code}` (no code) -/

/-- The caller's stack argument: `v5`'s slot, at `SP + 24`, holds 7 in `m0` (`argFacts`). -/
theorem argOK0 (harg : argFacts = true) (hid : (val 5).id = 5) : ArgOK E lc s0 (val 5) m0 := by
  intro _ x k o y hx hh hs hy
  unfold argFacts at harg
  obtain ⟨x', k', y', hx', hh', h24, h8, hrd, hy7⟩ := argFactsAt_spec harg
  rw [hid] at hh hy
  rw [hx] at hx'
  cases hx'
  rw [hh] at hh'
  cases hh'
  rw [hs] at h24
  cases h24
  rw [hy] at hrd
  cases hrd
  rw [hid, hy7]
  unfold SlotRel
  rw [h8]
  exact Or.inl (by simp only [m0, E]; decide)

/-- The per-value premises of G54 on `v5`, `Arg`: none of them applies. -/
theorem pre54 (hop : (val 5).op = .Arg) : G54Pre lc s0 (val 5) := by
  have hne : ∀ o : Op, o ≠ .Arg → (val 5).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩,
    ?_, ?_⟩, ?_⟩, fun h => absurd h (hne _ (by decide)), fun h => absurd h (hne _ (by decide))⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl
  · intro _ _ hl; rw [hop] at hl; cases hl
  · intro h; rcases h with h | h | h <;> exact absurd h (hne _ (by decide))
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ hl; rw [hop] at hl; cases hl
  · intro _ _ _ hl; rw [hop] at hl; simp [fp2Of] at hl
  · intro _ _ _ _ hl; rw [hop] at hl; simp [fp3Of] at hl
  · intro _ _ _ _ hpo; rw [hop] at hpo; simp [pairOp50] at hpo
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))

/-- **G62 on `runtime.syscall_Exit`'s ABI0 wrapper** (`v5 = Arg {code}`, the incoming stack
argument, no code): `checkG61` rejects the function and `checkG62` accepts it. From the first
state of an activation on `code = 7`, `stepLoc` runs `v5` to the slot of `code` holding 7, and
`g62_value` (at the mode `false`, the function needing no G48 mode), given the caller's word 7 at
`SP + 24` (`ArgOK`), relates it to a machine state whose word at `SP + 24`, the slot, is 7, under
an activation extending `E` that is again a `G49Env`. -/
theorem genG62_witness :
    (checkG61 lc0 ps bs g).toOption = none ∧
      ∃ s1 E1 m1 k, stepLoc GenG2.env lc s0 (val 5) = .ok s1 ∧ lc.home 5 = some (.slot k) ∧
        s1.slots.lookup k = some (.int .w64 7) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 1 m1 ∧
        (readMem m1.mem (GenG2.sp0 + BitVec.ofInt 64 24) 8).setWidth 64 = 7 := by
  obtain ⟨hl, hc, h61, hav, hfit, h48, hm1, hb, hv5, hi0, hop, hid, hro, hu0, harg, hrun, h7⟩ :=
    facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  obtain ⟨k, hk, hlook⟩ := holds7_spec hr
  have hE := g62Env hc hl hav hfit
  have hne : ∀ o : Op, o ≠ .Arg → (val 5).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  -- `g62_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 5 = some (val 5) := by
    rw [← liveCtx_ctx (lc := lc0)]; exact hv5
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -, -⟩ := g62_value (H := GenG2.H0) (env := GenG2.env)
    (osp := false) hc hE hl0 hm0 hb0 hi0 hv0 (by rw [hop]; rfl) locMatch0 g62Inv0
    (fun h => by cases h) (fun h => by cases h)
    (fun h => by
      have h' : needs48 lc = true := h
      rw [h48] at h'
      cases h')
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 0); rw [hu0]; intro e he; cases he)
    (pre54 hop) (ro0 hro)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => by cases h) (argOK0 harg hid) hs1
  refine ⟨h61, s1, E1, m1, k, hs1, hk, hlook, hx1, hE1, hp1, hm1', ?_⟩
  obtain ⟨o, ho, hrel⟩ := hm1'.slots k _ hlook
  obtain ⟨hEq, -⟩ := hx1
  have hslot : E1.slot = E.slot := by rw [hEq]
  have hsp : E1.sp = E.sp := by rw [hEq]
  have hlc : E1.lc = E.lc := by rw [hEq]
  have harg' := harg
  unfold argFacts at harg'
  obtain ⟨x', k', y', -, hh', h24, h8, -, -⟩ := argFactsAt_spec harg'
  rw [hk] at hh'
  cases hh'
  rw [hslot, h24] at ho
  cases ho
  unfold SlotRel at hrel
  rw [hlc, h8, hsp] at hrel
  rcases hrel with h | ⟨hn, -⟩
  · exact h
  · exact absurd h7 hn

end GoFV.Proof.Witness.GenG62
