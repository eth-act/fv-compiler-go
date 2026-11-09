import GoFV.Proof.Gen.G32
import GoFV.Proof.Witness.GenG13

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G32 of the genssa validator on `or64` and `runtime.funpack64`

Two functions of the corpus `gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim: no
small function holds both a register `OR` and an `ORconst` after `trim`.

* `test/armimm/main/or64,1.ssa` and `…,1.prog` (`fSsa`, `fProg`):

  ```go
  func or64(x uint64) uint64 {
  	return x | c64a // c64a = 0x00aa00dd55000066
  }
  ```

  Block `b1`: `v6 = ArgIntReg` (in `R0`), `InitMem`, `v3 = MOVDconst [c64a]` (`MOVD $c64a, R1`),
  `v9 = OR v6 v3` (`ORR R1, R0, R0`), `MakeResult`, then the `RET`.
* `std/std/runtime/funpack64,1.ssa` and `…,1.prog` (`fSsaK`, `fProgK`; `runtime/softfloat64.go`):
  in `funpack64`'s `default` case, `mant |= 1 << mantbits64`. Block `b10`:
  `v56 = ORconst [1 << 52] v17` (`ORR $0x10000000000000, R1, R1`), then `v59 = SUBconst`.

`checkG30` rejects both (`ORconst`, `OR` are G32's ops); `checkG32` accepts them with the PC
tables `tab`, `tabK` and the class tables `kt`, `ktK`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g32_facts`),
`stepLoc` runs `v9` from a state with `x = 0x1234` in `R0` and `c64a` in `R1`: `R0` then holds
`0x1234 ||| c64a`; and `v56` from a state with the mantissa `0x123456789abcd` in `R1`: `R1` then
holds `0x123456789abcd ||| 1 << 52`. On a framed activation with `G28Env`, `g32_value` runs the
`ORR R1, R0, R0` (`genG32_bin_witness`: the machine's `X0` is `0x1234 ||| c64a`) and the
`ORR $0x10000000000000, R1, R1` (`genG32_binK_witness`: the machine's `X1` is
`0x123456789abcd ||| 0x10000000000000`).
-/

namespace GoFV.Proof.Witness.GenG32

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-! ## The activation -/

/-- P0's layout of `ps`: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def Lof (ps : Array GoFV.Asm.Prog) : Link :=
  Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) of `lc` with the
globals at `symA` and the PC table `tab`. -/
def Eof (lc : LocCtx) (ps : Array GoFV.Asm.Prog) (tab : PcTab) : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- `Eof` is a `G28Env` of a function `checkG32` accepts, with no frame variable or home slot. -/
theorem envOf {lc : LocCtx} {ps : Array GoFV.Asm.Prog} {bs : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hc : checkG32 lc ps bs g = .ok (tab, kt))
    (hl : lc.ctx.f.lowered = true) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) :
    G28Env lc g (Lof ps) ps 0 tab (Eof lc ps tab) where
  env := {
    env := {
      env := {
        env := {
          lcEq := rfl
          link := rfl
          pcOf := rfl
          retOut := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG32_spec hl hc
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -⟩ := checkG32_spec hl hc
            intro y
            have hs : (Lof ps).sym y = GenG2.symA := rfl
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

/-- The empty memory. -/
def mem0 : Mem := {}

theorem memInj0 (mm : Memory) : MemInj GenG12.ι mem0 mm where
  nil := rfl
  mapped := by intro b al h; simp [mem0] at h
  inj := by intro b al b' al' a a' h; simp [mem0] at h
  bytes := ⟨fun _ _ => False, by intro b al a h; simp [mem0] at h⟩

/-! ## `or64` -/

/-- `test/armimm/main/or64,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "or64" 1 0 0
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
type t2 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t1 FUNC 8 8 8 hasptr,direct "func(uint64) uint64" "func(uint64) uint64" 0 1 1
field 0 "x" t2 ? 0
field 1 "" t2 ? 0
aux a2 sym "main.or64" "main.or64" 1 - 0 - - - - 0
posbase p2 "./armimm.go" 1 1 -1
aux a3 name "x" "x" PPARAM t2 0 1 used p2:85:11:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t2 0 1 - p2:85:21:0:0
aux a1 call "AuxCall{main.or64}" a2 1 1 1 8 8 1 1
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
type t11 INT 8 8 0 comparable,named "int" "int"
type t12 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t13 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
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
type t33 PTR 8 8 8 hasptr,direct,comparable "*uint64" "*uint64" t2
type t34 RESULTS ? ? ? - "uint64,mem" "" 2 t2,t28
slot s1 a3 t2 0 - 0
f b1 t1 a1 10 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t2,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:0:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,47851696654647398=v8
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,47851696654647398=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:86:86
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,47851696654647398=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:86:86
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:86:86
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:86:86
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:86:86
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:86:86
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:86:86
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:86:86
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:86:86
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:85:6:2:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "x+0" a3 0
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t33 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t33 0 a4 p2:86:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,47851696654647398=v8
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t33 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t33 0 a4 p2:86:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,47851696654647398=v8
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t33 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t33 0 a4 p2:86:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,47851696654647398=v8
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t33 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t33 0 a4 p2:86:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,47851696654647398=v8
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v8 Const64 t2 47851696654647398 - p0:0:0:0:0 1 -
v v9 Or64 t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 47851696654647398=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64ORconst t2 47851696654647398 - p2:86:11:1:0 1 v6
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64ORconst t2 47851696654647398 - p2:86:11:1:0 1 v6
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:86:86
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v8
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{main.or64}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v3
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v5,v7
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
fstate scheduled,laidout
regalloc 11 v3:R1,v6:R0,v9:R0,v10:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v3
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v5,v7
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
fstate scheduled,laidout
regalloc 11 v3:R1,v6:R0,v9:R0,v10:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 10 1
b b1 Ret p2:86:13:1:0 0 0 - v10 - -
v v6 ArgIntReg t2 0 a5 p2:86:13:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 ARM64MOVDconst t2 47851696654647398 - p2:86:11:1:0 1 -
v v9 ARM64OR t2 0 - p2:86:11:1:0 1 v6,v3
v v10 MakeResult t34 0 - p2:86:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v5,v7
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:86:86
fstate scheduled,laidout
regalloc 11 v3:R1,v6:R0,v9:R0,v10:[]
dcllen 2
end
frontend
end
ptrcache t5,t6,t7,t8,t10,t11,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t2,t11,t14,t15,t25,t26,t12,t13,t3,t17,t18,t19,t33,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t34
eof
"#

/-- `test/armimm/main/or64,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "or64" 1
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
type t1 8 8 0 0 - "uint64"
name n1 "x" PPARAM t1 1 "main.x" 0 a3
name n2 "~r0" PPARAMOUT t1 1 "main.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p2 "./armimm.go" 1 1 -1 1 "./armimm.go" "./armimm.go" 1 1
sym y1 "main.or64" 1
curfn p2:85:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 85 200080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "main.or64.arginfo1" 0
sym y4 "main.or64.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:85:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:85:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:85:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:85:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:85:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:85:6:2:0
p 6 6 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/47851696654647398/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:86:11:1:0
p 7 7 0 0 0 - ORR 0 REG/8193/0/0/NONE/0/0/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:86:11:2:0
p 8 8 0 0 0 - RET 0 _ 0 - _ 0 0 p2:86:13:2:0
p 9 9 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 85 200080
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
dbgpc 1:9:8
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p2:85:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:85:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:85:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:85:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:85:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:85:6:2:0
p 6 0 0 0 322 - MOVD 0 CONST/0/0/0/NONE/29/47851696654647398/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:86:11:1:0
p 7 16 0 0 49 - ORR 0 REG/8193/0/0/NONE/2/0/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:86:11:2:0
p 8 20 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:86:13:2:0
fn y1 8 0 0 0 85 2000c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 32 0 c10c80d201a0aaf2a11bc0f24115e0f2000001aac0035fd60000000000000000 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 0 1 28000 - 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040800 0
data y9 SRODATA 3 1 28000 020800 0
data y10 SRODATA 3 1 28000 040800 0
data y11 SRODATA 4 1 28000 ae010800 0
data y12 SRODATA 3 1 28000 000800 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.uint64" 0
sym y18 "type:uint64" 0
dwfn y13 y14 y15 - y16 "main.or64" 1:85 1 0 1 21
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "uint64" 0 0 1 p2:85:11:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uint64" 0 0 1 p2:85:21:0:0
var 0 0 "x" 5 1 0 0 0 8 y17 "./armimm.go" 85 11 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y17 "./armimm.go" 85 21 0 1 0 0 -
scope 0 0 - 0,1
data y13 SDWARFFCN 47 0 0 036d61696e2e6f723634000020019c0200000055012d7800005500000000000000002e7e7230000155000000000000 5
reloc 0 0 R_USETYPE 0 y18
reloc 11 1 R_DWTXTADDR_U1 0 y1
reloc 26 4 R_DWARFSECREF 0 y17
reloc 30 4 R_DWARFSECREF 0 y14
reloc 41 4 R_DWARFSECREF 0 y17
data y14 SDWARFLOC 8 0 0 0100040014015000 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y16 SDWARFLINES 24 0 0 0009020000000000000000040203d0001406af0210000101 1
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

/-- The PC table `checkG32` gives (`b1`: one entry per value `v6`, `v1`, `v3`, `v9`, `v10`, then
the `RET`). -/
def tab : PcTab := [(1, [5, 5, 5, 7, 8, 8])]

/-- The class table `checkG32` gives. -/
def kt : KTab := (match checkG32 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

def L : Link := Lof ps

def E : MatchEnv := Eof lc ps tab

/-- `c64a`. -/
def c64a : BitVec 64 := 0xaa00dd55000066

/-- The `runLoc` state before `v9`: `x = 0x1234` in `R0`, `c64a` in `R1`, every other register
`poison`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 0 then .int .w64 0x1234 else if i.val = 1 then .int .w64 c64a else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v9`: `X0 = 0x1234`, `X1 = c64a`, the activation's `g` and `FP`, the PC of
`v9`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 0 then 0x1234 else if k = 1 then c64a else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 3, mem := fun _ => 0 }

/-- The register holds the 64-bit integer `0x1234 ||| c64a`. -/
def isRes : Option Val → Bool
  | some (.int .w64 x) => x == 0x1234 ||| c64a
  | _ => false

theorem isRes_spec {o : Option Val} (h : isRes o = true) :
    o = some (.int .w64 (0x1234 ||| c64a)) := by
  unfold isRes at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on `or64`: it holds an arm64 op, `checkG32` accepts it with
`tab` and `kt` and `checkG30` does not; it accesses no frame variable and has no home slot; `b1`
holds `v9` (`OR`) at index 3, `R0` and `R1` have class 64 before `v9` and the upper-bit table is
empty there; `stepLoc` runs `v9` from `s0` to `R0 = 0x1234 ||| c64a`. -/
def gFactsOr : Bool :=
  lc.ctx.f.lowered &&
    (checkG32 lc ps bs g).toOption == some (tab, kt) && (checkG30 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 9).isSome && blk1.values[3]? == some 9 && (val 9).op == .ARM64OR &&
    (kAt lc kt 1 blk1 3).get 0 == some 64 && (kAt lc kt 1 blk1 3).get 1 == some 64 &&
    uL lc blk1 3 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 9)) fun s1 => isRes s1.regs[0]?

/-! ## `runtime.funpack64` -/

/-- `std/std/runtime/funpack64,1.ssa` (quick-v10). -/
def fSsaK : String := r#"gofv-ssa 5.1
pkg "runtime"
func "funpack64" 1 0 0
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
type t2 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t3 INT 8 8 0 comparable,named "int" "int"
type t4 BOOL 1 1 0 comparable,named "bool" "bool"
type t1 FUNC 8 8 8 hasptr,direct "func(uint64) (uint64, uint64, int, bool, bool)" "func(uint64) (uint64, uint64, int, bool, bool)" 0 1 5
field 0 "f" t2 ? 0
field 1 "sign" t2 ? 0
field 2 "mant" t2 ? 0
field 3 "exp" t3 ? 0
field 4 "inf" t4 ? 0
field 5 "nan" t4 ? 0
aux a2 sym "runtime.funpack64" "runtime.funpack64" 1 - 0 - - - - 0
posbase p186 "runtime/softfloat64.go" 1 1 -1
aux a3 name "f" "f" PPARAM t2 0 1 used p186:29:16:0:0
aux a4 name "sign" "sign" PPARAMOUT t2 0 1 used p186:29:27:0:0
aux a5 name "mant" "mant" PPARAMOUT t2 0 1 used p186:29:33:0:0
aux a6 name "exp" "exp" PPARAMOUT t3 0 1 used p186:29:46:0:0
aux a7 name "inf" "inf" PPARAMOUT t4 0 1 used p186:29:55:0:0
aux a8 name "nan" "nan" PPARAMOUT t4 0 1 used p186:29:60:0:0
aux a1 call "AuxCall{runtime.funpack64}" a2 1 1 5 8 8 1 5
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
abiparam out 1 t2 a5 1 -1
abiparam out 2 t3 a6 2 -1
abiparam out 3 t4 a7 3 -1
abiparam out 4 t4 a8 4 -1
type t5 INT8 1 1 0 comparable,named "int8" "int8"
type t6 INT16 2 2 0 comparable,named "int16" "int16"
type t7 INT32 4 4 0 comparable,named "int32" "int32"
type t8 INT64 8 8 0 comparable,named "int64" "int64"
type t9 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t10 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t11 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t12 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t13 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t9
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t7
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t11
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t3
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
type t33 PTR 8 8 8 hasptr,direct,comparable "*uint64" "*uint64" t2
type t34 PTR 8 8 8 hasptr,direct,comparable "*bool" "*bool" t4
type t35 RESULTS ? ? ? - "uint64,uint64,int,bool,bool,mem" "" 6 t2,t2,t3,t4,t4,t28
slot s1 a3 t2 0 - 0
f b1 t1 a1 77 18
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t8,UInt8=t9,UInt16=t10,UInt32=t11,UInt64=t2,Int=t3,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 If p186:43:7:0:0 0 0 - v23 b4:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 11 -
v v2 SP t15 0 - p0:0:0:0:0 6 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t33 0 a5 p0:0:0:0:0 0 v2,v1
v v7 LocalAddr t20 0 a6 p0:0:0:0:0 0 v2,v1
v v8 LocalAddr t34 0 a7 p0:0:0:0:0 0 v2,v1
v v9 LocalAddr t34 0 a8 p0:0:0:0:0 0 v2,v1
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 8 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:0:0 5 v10,v14
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:0:0 3 v10,v16
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 0 - p186:32:13:0:0 1 v10,v18
v v20 Copy t3 0 - p186:32:13:2:0 1 v19
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v20,v21
v v23 Eq64 t4 0 - p186:43:2:0:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v53 Const64 t3 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v60 Phi t2 0 - p186:58:2:0:0 1 v76,v15
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v63 Phi t4 0 - p186:58:2:0:0 1 v72,v13
v v64 Phi t4 0 - p186:58:2:0:0 1 v70,v13
v v65 Phi t28 0 - p186:58:2:0:0 1 v68,v1
v v66 MakeResult t35 0 - p186:58:2:0:0 1 v60,v61,v62,v63,v64,v65
b b3 Plain p186:53:2:1:0 0 0 - - b10:0 b7:0
b b4 Plain p186:43:2:1:0 0 0 - - b6:0 b1:0
b b5 If p186:35:20:0:0 0 0 - v25 b8:0,b7:0 b1:1
v v24 Copy t3 0 - p186:35:2:2:0 1 v22
v v25 Eq64 t4 0 - p186:35:2:0:0 1 v24,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b4:0
v v41 Copy t2 0 - p186:45:11:2:0 3 v17
v v42 Neq64 t4 0 - p186:45:11:0:0 1 v41,v11
b b7 Plain p186:53:2:1:0 0 0 - - b3:0 b5:1
b b8 Plain p186:35:2:1:0 0 0 - - b9:0 b5:0
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b8:0
v v26 Copy t2 0 - p186:36:11:2:0 3 v17
v v27 Neq64 t4 0 - p186:36:11:0:0 1 v26,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b3:0
v v55 Copy t2 0 - p186:55:8:2:0 1 v17
v v56 Or64 t2 0 - p186:55:8:0:0 1 v55,v47
v v57 Copy t3 0 - p186:56:7:2:0 1 v22
v v59 Add64 t3 0 - p186:56:7:0:0 1 v57,v58
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v35 Copy t2 0 - p186:41:3:2:0 1 v15
v v36 Copy t2 0 - p186:41:3:2:0 1 v26
v v37 Copy t3 0 - p186:41:3:2:0 1 v22
v v38 Copy t4 0 - p186:41:3:2:0 1 v13
v v39 Copy t28 0 - p186:41:3:2:0 1 v1
v v40 MakeResult t35 0 - p186:41:3:0:0 1 v35,v36,v37,v28,v38,v39
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v29 Copy t2 0 - p186:38:4:2:0 1 v15
v v30 Copy t2 0 - p186:38:4:2:0 1 v26
v v31 Copy t3 0 - p186:38:4:2:0 1 v22
v v32 Copy t4 0 - p186:38:4:2:0 1 v13
v v33 Copy t28 0 - p186:38:4:2:0 1 v1
v v34 MakeResult t35 0 - p186:38:4:0:0 1 v29,v30,v31,v32,v28,v33
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v68 Phi t28 0 - p186:45:3:0:0 1 v1,v69
v v70 Phi t4 0 - p186:45:3:0:0 1 v13,v71
v v72 Phi t4 0 - p186:45:3:0:0 1 v13,v73
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v41,v46
v v76 Phi t2 0 - p186:45:3:0:0 1 v15,v77
b b14 Plain p186:47:4:0:0 0 0 - - b15:0 b6:0
v v43 Copy t3 0 - p186:46:8:2:0 1 v22
v v45 Add64 t3 0 - p186:46:8:0:0 1 v43,v44
b b15 If p186:47:16:0:0 1 0 - v48 b16:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v41,v51
v v48 Less64U t4 0 - p186:47:13:0:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
v v69 Copy t28 0 - p186:58:2:2:0 1 v1
v v71 Copy t4 0 - p186:58:2:2:0 1 v13
v v73 Copy t4 0 - p186:58:2:2:0 1 v13
v v77 Copy t2 0 - p186:58:2:2:0 1 v15
b b16 Plain p186:49:8:0:0 0 0 - - b17:0 b15:0
v v49 Copy t2 0 - p186:48:10:2:0 1 v46
v v51 Lsh64x64 t2 0 - p186:48:10:0:0 1 v49,v50
v v52 Copy t3 0 - p186:49:8:2:0 1 v67
v v54 Sub64 t3 0 - p186:49:8:0:0 1 v52,v53
b b17 Plain p186:47:16:0:0 0 0 - - b15:1 b16:0
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,v53,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev -
freeb -
dcllen 7
end
pass 1 "number lines"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b4:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 11 -
v v2 SP t15 0 - p0:0:0:0:0 6 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t33 0 a5 p0:0:0:0:0 0 v2,v1
v v7 LocalAddr t20 0 a6 p0:0:0:0:0 0 v2,v1
v v8 LocalAddr t34 0 a7 p0:0:0:0:0 0 v2,v1
v v9 LocalAddr t34 0 a8 p0:0:0:0:0 0 v2,v1
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 8 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 5 v10,v14
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 3 v10,v16
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 0 - p186:32:13:1:0 1 v10,v18
v v20 Copy t3 0 - p186:32:13:2:0 1 v19
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v20,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v53 Const64 t3 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v60 Phi t2 0 - p186:58:2:0:0 1 v76,v15
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v63 Phi t4 0 - p186:58:2:0:0 1 v72,v13
v v64 Phi t4 0 - p186:58:2:0:0 1 v70,v13
v v65 Phi t28 0 - p186:58:2:0:0 1 v68,v1
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v60,v61,v62,v63,v64,v65
b b3 Plain p186:53:2:1:0 0 0 - - b10:0 b7:0
b b4 Plain p186:43:2:1:0 0 0 - - b6:0 b1:0
b b5 If p186:35:20:0:0 0 0 - v25 b8:0,b7:0 b1:1
v v24 Copy t3 0 - p186:35:2:2:0 1 v22
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v24,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b4:0
v v41 Copy t2 0 - p186:45:11:2:0 3 v17
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v41,v11
b b7 Plain p186:53:2:1:0 0 0 - - b3:0 b5:1
b b8 Plain p186:35:2:1:0 0 0 - - b9:0 b5:0
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b8:0
v v26 Copy t2 0 - p186:36:11:2:0 3 v17
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v26,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b3:0
v v55 Copy t2 0 - p186:55:8:2:0 1 v17
v v56 Or64 t2 0 - p186:55:8:1:0 1 v55,v47
v v57 Copy t3 0 - p186:56:7:2:0 1 v22
v v59 Add64 t3 0 - p186:56:7:1:0 1 v57,v58
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v35 Copy t2 0 - p186:41:3:2:0 1 v15
v v36 Copy t2 0 - p186:41:3:2:0 1 v26
v v37 Copy t3 0 - p186:41:3:2:0 1 v22
v v38 Copy t4 0 - p186:41:3:2:0 1 v13
v v39 Copy t28 0 - p186:41:3:2:0 1 v1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v35,v36,v37,v28,v38,v39
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v29 Copy t2 0 - p186:38:4:2:0 1 v15
v v30 Copy t2 0 - p186:38:4:2:0 1 v26
v v31 Copy t3 0 - p186:38:4:2:0 1 v22
v v32 Copy t4 0 - p186:38:4:2:0 1 v13
v v33 Copy t28 0 - p186:38:4:2:0 1 v1
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v29,v30,v31,v32,v28,v33
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v68 Phi t28 0 - p186:45:3:0:0 1 v1,v69
v v70 Phi t4 0 - p186:45:3:0:0 1 v13,v71
v v72 Phi t4 0 - p186:45:3:0:0 1 v13,v73
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v41,v46
v v76 Phi t2 0 - p186:45:3:0:0 1 v15,v77
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v43 Copy t3 0 - p186:46:8:2:0 1 v22
v v45 Add64 t3 0 - p186:46:8:1:0 1 v43,v44
b b15 If p186:47:16:0:0 1 0 - v48 b16:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v41,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
v v69 Copy t28 0 - p186:58:2:2:0 1 v1
v v71 Copy t4 0 - p186:58:2:2:0 1 v13
v v73 Copy t4 0 - p186:58:2:2:0 1 v13
v v77 Copy t2 0 - p186:58:2:2:0 1 v15
b b16 Plain p186:49:8:0:0 0 0 - - b17:0 b15:0
v v49 Copy t2 0 - p186:48:10:2:0 1 v46
v v51 Lsh64x64 t2 0 - p186:48:10:1:0 1 v49,v50
v v52 Copy t3 0 - p186:49:8:2:0 1 v67
v v54 Sub64 t3 0 - p186:49:8:1:0 1 v52,v53
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b16:0
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,v53,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev -
freeb -
cache postorder b17,b16,b2,b13,b18,b15,b14,b6,b4,b12,b11,b9,b8,b10,b3,b7,b5,b1
cache linestarts 186:30:58
dcllen 7
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b4:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 14 -
v v2 SP t15 0 - p0:0:0:0:0 6 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t33 0 a5 p0:0:0:0:0 0 v2,v1
v v7 LocalAddr t20 0 a6 p0:0:0:0:0 0 v2,v1
v v8 LocalAddr t34 0 a7 p0:0:0:0:0 0 v2,v1
v v9 LocalAddr t34 0 a8 p0:0:0:0:0 0 v2,v1
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 12 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 8 v10,v14
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 12 v10,v16
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 0 - p186:32:13:1:0 2 v10,v18
v v20 Copy t3 0 - p186:32:13:2:0 0 v19
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 12 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v53 Const64 t3 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v60 Copy t2 0 - p186:58:2:0:0 0 v15
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v63 Copy t4 0 - p186:58:2:0:0 0 v13
v v64 Copy t4 0 - p186:58:2:0:0 0 v13
v v65 Copy t28 0 - p186:58:2:0:0 0 v1
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b3 Plain p186:53:2:1:0 0 0 - - b10:0 b7:0
b b4 Plain p186:43:2:1:0 0 0 - - b6:0 b1:0
b b5 If p186:35:20:0:0 0 0 - v25 b8:0,b7:0 b1:1
v v24 Copy t3 0 - p186:35:2:2:0 0 v22
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b4:0
v v41 Copy t2 0 - p186:45:11:2:0 0 v17
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b7 Plain p186:53:2:1:0 0 0 - - b3:0 b5:1
b b8 Plain p186:35:2:1:0 0 0 - - b9:0 b5:0
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b8:0
v v26 Copy t2 0 - p186:36:11:2:0 0 v17
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b3:0
v v55 Copy t2 0 - p186:55:8:2:0 0 v17
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v57 Copy t3 0 - p186:56:7:2:0 0 v22
v v59 Add64 t3 0 - p186:56:7:1:0 1 v22,v58
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v35 Copy t2 0 - p186:41:3:2:0 0 v15
v v36 Copy t2 0 - p186:41:3:2:0 0 v17
v v37 Copy t3 0 - p186:41:3:2:0 0 v22
v v38 Copy t4 0 - p186:41:3:2:0 0 v13
v v39 Copy t28 0 - p186:41:3:2:0 0 v1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v17,v22,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v29 Copy t2 0 - p186:38:4:2:0 0 v15
v v30 Copy t2 0 - p186:38:4:2:0 0 v17
v v31 Copy t3 0 - p186:38:4:2:0 0 v22
v v32 Copy t4 0 - p186:38:4:2:0 0 v13
v v33 Copy t28 0 - p186:38:4:2:0 0 v1
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v22,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v68 Copy t28 0 - p186:45:3:0:0 0 v1
v v70 Copy t4 0 - p186:45:3:0:0 0 v13
v v72 Copy t4 0 - p186:45:3:0:0 0 v13
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
v v76 Copy t2 0 - p186:45:3:0:0 0 v15
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v43 Copy t3 0 - p186:46:8:2:0 0 v22
v v45 Add64 t3 0 - p186:46:8:1:0 1 v22,v44
b b15 If p186:47:16:0:0 1 0 - v48 b16:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 3 v45,v54
v v69 Copy t28 0 - p186:58:2:2:0 0 v1
v v71 Copy t4 0 - p186:58:2:2:0 0 v13
v v73 Copy t4 0 - p186:58:2:2:0 0 v13
v v77 Copy t2 0 - p186:58:2:2:0 0 v15
b b16 Plain p186:49:8:0:0 0 0 - - b17:0 b15:0
v v49 Copy t2 0 - p186:48:10:2:0 0 v46
v v51 Lsh64x64 t2 0 - p186:48:10:1:0 1 v46,v50
v v52 Copy t3 0 - p186:49:8:2:0 0 v67
v v54 Sub64 t3 0 - p186:49:8:1:0 1 v67,v53
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b16:0
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,v53,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev -
freeb -
cache postorder b17,b16,b2,b13,b18,b15,b14,b6,b4,b12,b11,b9,b8,b10,b3,b7,b5,b1
cache linestarts 186:30:58
dcllen 7
end
pass 3 "early deadcode"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b4:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v10,v14
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 7 v10,v16
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 0 - p186:32:13:1:0 1 v10,v18
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v53 Const64 t3 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b3 Plain p186:53:2:1:0 0 0 - - b10:0 b7:0
b b4 Plain p186:43:2:1:0 0 0 - - b6:0 b1:0
b b5 If p186:35:20:0:0 0 0 - v25 b8:0,b7:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b4:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b7 Plain p186:53:2:1:0 0 0 - - b3:0 b5:1
b b8 Plain p186:35:2:1:0 0 0 - - b9:0 b5:0
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b8:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b3:0
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v22,v58
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v17,v22,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v22,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v45 Add64 t3 0 - p186:46:8:1:0 1 v22,v44
b b15 If p186:47:16:0:0 1 0 - v48 b16:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
b b16 Plain p186:49:8:0:0 0 0 - - b17:0 b15:0
v v51 Lsh64x64 t2 0 - p186:48:10:1:0 1 v46,v50
v v54 Sub64 t3 0 - p186:49:8:1:0 1 v67,v53
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b16:0
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,v53,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v52,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb -
cache postorder b17,b16,b2,b13,b18,b15,b14,b6,b4,b12,b11,b9,b8,b10,b3,b7,b5,b1
cache linestarts 186:30:58
dcllen 7
end
pass 4 "short circuit"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v10,v14
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 7 v10,v16
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 0 - p186:32:13:1:0 1 v10,v18
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v53 Const64 t3 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b3 BlockInvalid p186:53:2:1:0 0 0 - - - -
b b4 BlockInvalid p186:43:2:1:0 0 0 - - - -
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b7 BlockInvalid p186:53:2:1:0 0 0 - - - -
b b8 BlockInvalid p186:35:2:1:0 0 0 - - - -
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v22,v58
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v17,v22,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v22,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v45 Add64 t3 0 - p186:46:8:1:0 1 v22,v44
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
b b16 BlockInvalid p186:49:8:0:0 0 0 - - - -
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 0 - p186:48:10:1:0 1 v46,v50
v v54 Sub64 t3 0 - p186:49:8:1:0 1 v67,v53
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,v53,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v52,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb -
cache linestarts 186:30:58
dcllen 7
end
pass 5 "decompose user"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v10,v14
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 7 v10,v16
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 0 - p186:32:13:1:0 1 v10,v18
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v53 Const64 t3 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b3 BlockInvalid p186:53:2:1:0 0 0 - - - -
b b4 BlockInvalid p186:43:2:1:0 0 0 - - - -
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b7 BlockInvalid p186:53:2:1:0 0 0 - - - -
b b8 BlockInvalid p186:35:2:1:0 0 0 - - - -
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v22,v58
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v17,v22,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v22,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v45 Add64 t3 0 - p186:46:8:1:0 1 v22,v44
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
b b16 BlockInvalid p186:49:8:0:0 0 0 - - - -
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 0 - p186:48:10:1:0 1 v46,v50
v v54 Sub64 t3 0 - p186:49:8:1:0 1 v67,v53
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,v53,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v52,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb -
cache linestarts 186:30:58
dcllen 7
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v10,v14
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 7 v10,v16
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 0 - p186:32:13:1:0 1 v10,v18
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v53 Const64 t3 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v22,v58
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v17,v22,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v22,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v45 Add64 t3 0 - p186:46:8:1:0 1 v22,v44
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 0 - p186:48:10:1:0 1 v46,v50
v v54 Sub64 t3 0 - p186:49:8:1:0 1 v67,v53
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,v53,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v52,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache linestarts 186:30:58
dcllen 7
end
pass 7 "opt"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v10,v14
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 7 v10,v16
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v22,v58
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v17,v22,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v22,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v45 Add64 t3 0 - p186:46:8:1:0 1 v22,v44
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v52,v67
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache linestarts 186:30:58
dcllen 7
end
pass 8 "zero arg cse"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v10,v14
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 7 v10,v16
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v22,v58
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v17,v22,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v22,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v45 Add64 t3 0 - p186:46:8:1:0 1 v22,v44
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v52,v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache linestarts 186:30:58
dcllen 7
end
pass 9 "opt deadcode"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v10,v14
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 7 v10,v16
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v22,v58
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v17,v22,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v22,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v45 Add64 t3 0 - p186:46:8:1:0 1 v22,v44
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v52,v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache linestarts 186:30:58
dcllen 7
end
pass 10 "generic cse"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 7 v16,v10
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v17,v22,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v22,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v45 Add64 t3 0 - p186:46:8:1:0 1 v44,v22
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 11 "phiopt"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 7 v16,v10
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v17,v22,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v22,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v45 Add64 t3 0 - p186:46:8:1:0 1 v44,v22
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 12 "gcse deadcode"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 7 v16,v10
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v17,v22,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v22,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v45 Add64 t3 0 - p186:46:8:1:0 1 v44,v22
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 13 "nilcheckelim"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 2 -
v v12 Const64 t3 0 - p0:0:0:0:0 1 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v17 And64 t2 0 - p186:31:11:1:0 7 v16,v10
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v21 Const64 t3 2047 - p0:0:0:0:0 2 -
v v22 And64 t3 0 - p186:32:27:0:0 7 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v17,v22,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v22,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v22,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v45 Add64 t3 0 - p186:46:8:1:0 1 v44,v22
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
v v67 Phi t3 0 - p186:47:13:0:0 2 v45,v54
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 14 "prove"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 3 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 2 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v45 Add64 t3 0 - p186:46:8:1:0 0 v44,v12
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 15 "divisible"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v45,v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58:46=14
dcllen 7
end
pass 16 "divmod"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v45,v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 17 "middle opt"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v45,v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 18 "known bits"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v45,v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 19 "early fuse"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 Arg t2 0 a3 p186:29:6:2:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v45,v53,v49,v77,v73,v71,v69,v43,v76,v72,v70,v68,v33,v32,v31,v30,v29,v39,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 20 "expand calls"
aux a9 nameoff "f+0" a3 0
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 18 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v45 SB t15 0 - p0:0:0:0:0 0 -
v v53 SP t15 0 - p0:0:0:0:0 16 -
v v49 OffPtr t33 0 - p0:0:0:0:0 0 v53
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
v v77 LocalAddr t33 0 a4 p186:58:2:1:0 0 v53,v1
v v73 LocalAddr t33 0 a5 p186:58:2:1:0 0 v53,v1
v v71 LocalAddr t20 0 a6 p186:58:2:1:0 0 v53,v1
v v69 LocalAddr t34 0 a7 p186:58:2:1:0 0 v53,v1
v v43 LocalAddr t34 0 a8 p186:58:2:1:0 0 v53,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
v v76 LocalAddr t33 0 a4 p186:41:3:1:0 0 v53,v1
v v72 LocalAddr t33 0 a5 p186:41:3:1:0 0 v53,v1
v v70 LocalAddr t20 0 a6 p186:41:3:1:0 0 v53,v1
v v68 LocalAddr t34 0 a7 p186:41:3:1:0 0 v53,v1
v v33 LocalAddr t34 0 a8 p186:41:3:1:0 0 v53,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
v v32 LocalAddr t33 0 a4 p186:38:4:1:0 0 v53,v1
v v31 LocalAddr t33 0 a5 p186:38:4:1:0 0 v53,v1
v v30 LocalAddr t20 0 a6 p186:38:4:1:0 0 v53,v1
v v29 LocalAddr t34 0 a7 p186:38:4:1:0 0 v53,v1
v v39 LocalAddr t34 0 a8 p186:38:4:1:0 0 v53,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,v49,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 21 "decompose builtin"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 18 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v45 SB t15 0 - p0:0:0:0:0 0 -
v v53 SP t15 0 - p0:0:0:0:0 16 -
v v49 OffPtr t33 0 - p0:0:0:0:0 0 v53
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
v v77 LocalAddr t33 0 a4 p186:58:2:1:0 0 v53,v1
v v73 LocalAddr t33 0 a5 p186:58:2:1:0 0 v53,v1
v v71 LocalAddr t20 0 a6 p186:58:2:1:0 0 v53,v1
v v69 LocalAddr t34 0 a7 p186:58:2:1:0 0 v53,v1
v v43 LocalAddr t34 0 a8 p186:58:2:1:0 0 v53,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
v v76 LocalAddr t33 0 a4 p186:41:3:1:0 0 v53,v1
v v72 LocalAddr t33 0 a5 p186:41:3:1:0 0 v53,v1
v v70 LocalAddr t20 0 a6 p186:41:3:1:0 0 v53,v1
v v68 LocalAddr t34 0 a7 p186:41:3:1:0 0 v53,v1
v v33 LocalAddr t34 0 a8 p186:41:3:1:0 0 v53,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
v v32 LocalAddr t33 0 a4 p186:38:4:1:0 0 v53,v1
v v31 LocalAddr t33 0 a5 p186:38:4:1:0 0 v53,v1
v v30 LocalAddr t20 0 a6 p186:38:4:1:0 0 v53,v1
v v29 LocalAddr t34 0 a7 p186:38:4:1:0 0 v53,v1
v v39 LocalAddr t34 0 a8 p186:38:4:1:0 0 v53,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,v49,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 22 "softfloat"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 18 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v45 SB t15 0 - p0:0:0:0:0 0 -
v v53 SP t15 0 - p0:0:0:0:0 16 -
v v49 OffPtr t33 0 - p0:0:0:0:0 0 v53
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
v v77 LocalAddr t33 0 a4 p186:58:2:1:0 0 v53,v1
v v73 LocalAddr t33 0 a5 p186:58:2:1:0 0 v53,v1
v v71 LocalAddr t20 0 a6 p186:58:2:1:0 0 v53,v1
v v69 LocalAddr t34 0 a7 p186:58:2:1:0 0 v53,v1
v v43 LocalAddr t34 0 a8 p186:58:2:1:0 0 v53,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
v v76 LocalAddr t33 0 a4 p186:41:3:1:0 0 v53,v1
v v72 LocalAddr t33 0 a5 p186:41:3:1:0 0 v53,v1
v v70 LocalAddr t20 0 a6 p186:41:3:1:0 0 v53,v1
v v68 LocalAddr t34 0 a7 p186:41:3:1:0 0 v53,v1
v v33 LocalAddr t34 0 a8 p186:41:3:1:0 0 v53,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
v v32 LocalAddr t33 0 a4 p186:38:4:1:0 0 v53,v1
v v31 LocalAddr t33 0 a5 p186:38:4:1:0 0 v53,v1
v v30 LocalAddr t20 0 a6 p186:38:4:1:0 0 v53,v1
v v29 LocalAddr t34 0 a7 p186:38:4:1:0 0 v53,v1
v v39 LocalAddr t34 0 a8 p186:38:4:1:0 0 v53,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,v49,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 23 "branchelim"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 18 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v45 SB t15 0 - p0:0:0:0:0 0 -
v v53 SP t15 0 - p0:0:0:0:0 16 -
v v49 OffPtr t33 0 - p0:0:0:0:0 0 v53
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
v v77 LocalAddr t33 0 a4 p186:58:2:1:0 0 v53,v1
v v73 LocalAddr t33 0 a5 p186:58:2:1:0 0 v53,v1
v v71 LocalAddr t20 0 a6 p186:58:2:1:0 0 v53,v1
v v69 LocalAddr t34 0 a7 p186:58:2:1:0 0 v53,v1
v v43 LocalAddr t34 0 a8 p186:58:2:1:0 0 v53,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
v v76 LocalAddr t33 0 a4 p186:41:3:1:0 0 v53,v1
v v72 LocalAddr t33 0 a5 p186:41:3:1:0 0 v53,v1
v v70 LocalAddr t20 0 a6 p186:41:3:1:0 0 v53,v1
v v68 LocalAddr t34 0 a7 p186:41:3:1:0 0 v53,v1
v v33 LocalAddr t34 0 a8 p186:41:3:1:0 0 v53,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
v v32 LocalAddr t33 0 a4 p186:38:4:1:0 0 v53,v1
v v31 LocalAddr t33 0 a5 p186:38:4:1:0 0 v53,v1
v v30 LocalAddr t20 0 a6 p186:38:4:1:0 0 v53,v1
v v29 LocalAddr t34 0 a7 p186:38:4:1:0 0 v53,v1
v v39 LocalAddr t34 0 a8 p186:38:4:1:0 0 v53,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,v49,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 24 "late opt"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v39,v29,v30,v31,v32,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 25 "dead auto elim"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v39,v29,v30,v31,v32,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 26 "sccp"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
v v39 Const64 t3 -1023 - p186:49:8:1:0 0 -
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v29,v30,v31,v32,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 27 "generic deadcode"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v39,v29,v30,v31,v32,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 28 "late fuse"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v39,v29,v30,v31,v32,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 29 "check bce"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v39,v29,v30,v31,v32,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 30 "dse"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v39,v29,v30,v31,v32,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 31 "memcombine"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v39,v29,v30,v31,v32,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 32 "writebarrier"
f b1 t1 a1 77 18
b b1 If p186:43:7:0:0 0 0 - v23 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 Const64 t2 0 - p0:0:0:0:0 3 -
v v12 Const64 t3 0 - p0:0:0:0:0 2 -
v v13 ConstBool t4 0 - p0:0:0:0:0 4 -
v v14 Const64 t2 -9223372036854775808 - p0:0:0:0:0 1 -
v v16 Const64 t2 4503599627370495 - p0:0:0:0:0 1 -
v v18 Const64 t14 52 - p0:0:0:0:0 1 -
v v21 Const64 t3 2047 - p0:0:0:0:0 4 -
v v28 ConstBool t4 1 - p0:0:0:0:0 2 -
v v44 Const64 t3 -1022 - p0:0:0:0:0 1 -
v v47 Const64 t2 4503599627370496 - p0:0:0:0:0 2 -
v v50 Const64 t14 1 - p0:0:0:0:0 1 -
v v52 Const64 t3 -1 - p186:49:8:1:0 1 -
v v58 Const64 t3 -1023 - p0:0:0:0:0 1 -
v v15 And64 t2 0 - p186:30:11:1:0 3 v14,v10
v v17 And64 t2 0 - p186:31:11:1:0 6 v16,v10
v v19 Rsh64Ux64 t2 1 - p186:32:13:1:0 1 v10,v18
v v22 And64 t3 0 - p186:32:27:0:0 3 v19,v21
v v23 Eq64 t4 0 - p186:43:2:1:0 1 v22,v12
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 If p186:35:20:0:0 0 0 - v25 b9:0,b10:0 b1:1
v v25 Eq64 t4 0 - p186:35:2:1:0 1 v22,v21
b b6 If p186:45:14:0:0 0 0 - v42 b14:0,b13:0 b1:0
v v42 Neq64 t4 0 - p186:45:11:1:0 1 v17,v11
b b9 If p186:36:14:0:0 0 0 - v27 b12:0,b11:0 b5:0
v v27 Neq64 t4 0 - p186:36:11:1:0 1 v17,v11
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 Or64 t2 0 - p186:55:8:1:0 1 v17,v47
v v59 Add64 t3 0 - p186:56:7:1:0 1 v58,v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 If p186:47:16:0:0 1 0 - v48 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v48 Less64U t4 0 - p186:47:13:1:0 1 v46,v47
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 Lsh64x64 t2 1 - p186:48:10:1:0 1 v46,v50
v v54 Add64 t3 0 - p186:49:8:1:0 1 v67,v52
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -9223372036854775808=v14,-1023=v58,-1022=v44,0=v11,v12,v13,1=v28,v50,52=v18,2047=v21,4503599627370495=v16,4503599627370496=v47
freev v39,v29,v30,v31,v32,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 33 "lower"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 ARM64MOVDconst t2 0 - p0:0:0:0:0 1 -
v v12 ARM64MOVDconst t3 0 - p0:0:0:0:0 1 -
v v13 ARM64MOVDconst t4 0 - p0:0:0:0:0 4 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMPconst t29 4503599627370496 - p186:47:13:1:0 1 v46
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64SLLconst t2 1 - p186:48:10:1:0 1 v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v48,v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58:49=1
dcllen 7
end
pass 34 "addressing modes"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 ARM64MOVDconst t2 0 - p0:0:0:0:0 1 -
v v12 ARM64MOVDconst t3 0 - p0:0:0:0:0 1 -
v v13 ARM64MOVDconst t4 0 - p0:0:0:0:0 4 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 3 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMPconst t29 4503599627370496 - p186:47:13:1:0 1 v46
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64SLLconst t2 1 - p186:48:10:1:0 1 v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v48,v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58:49=1
dcllen 7
end
pass 35 "late lower"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 36 "pair"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2
cache linestarts 186:30:58
dcllen 7
end
pass 38 "lowered cse"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
dcllen 7
end
pass 39 "elim unread autos"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
dcllen 7
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
dcllen 7
end
pass 41 "lowered deadcode"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
dcllen 7
end
pass 42 "checkLower"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
dcllen 7
end
pass 43 "loop invariant"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
dcllen 7
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
dcllen 7
end
pass 45 "tighten"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache loopnest 19 0 b15:-:2:1:1:0 b15:0,b17:0
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
dcllen 7
end
pass 46 "late deadcode"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b13:0 b1:0
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b6:1,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b16,b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:77,b2:b1:-:-:71:74,b5:b1:b10:b6:5:32,b6:b1:b14:b2:35:68,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:62:65,b14:b6:b15:b13:38:59,b15:b14:b18:-:41:56,b17:b15:-:-:50:53,b18:b15:-:b17:44:47
cache loopnest 19 0 b15:-:2:1:1:0 b15:0,b17:0
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
dcllen 7
end
pass 47 "critical"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b16:0 b1:0
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b16:0,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
b b16 Plain p186:45:14:1:0 0 0 - - b13:0 b6:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b8,b7,b4,b3
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
dcllen 7
end
pass 48 "phi tighten"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 0 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 0 0 - v17 b14:0,b16:0 b1:0
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b16:0,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
b b16 Plain p186:45:14:1:0 0 0 - - b13:0 b6:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b8,b7,b4,b3
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
dcllen 7
end
pass 49 "likelyadjust"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 1 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b6 ARM64NZ p186:45:14:1:0 1 0 - v17 b14:0,b16:0 b1:0
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b16:0,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
b b16 Plain p186:45:14:1:0 0 0 - - b13:0 b6:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b16,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b2:b1,b5:b1,b6:b1,b9:b5,b10:b5,b11:b9,b12:b9,b13:b6,b14:b6,b15:b14,b17:b15,b18:b15,b16:b6
cache sdom b1:-:b5:-:2:83,b2:b1:-:-:77:80,b5:b1:b10:b6:5:32,b6:b1:b16:b2:35:74,b9:b5:b11:-:14:29,b10:b5:-:b9:8:11,b11:b9:-:b12:17:20,b12:b9:-:-:23:26,b13:b6:-:-:68:71,b14:b6:b15:b13:44:65,b15:b14:b18:-:47:62,b17:b15:-:-:56:59,b18:b15:-:b17:50:53,b16:b6:-:b14:38:41
cache loopnest 19 0 b15:-:2:1:1:0 b15:0,b17:0
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
dcllen 7
end
pass 50 "layout"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 1 0 - v22 b6:0,b5:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
b b6 ARM64NZ p186:45:14:1:0 1 0 - v17 b14:0,b16:0 b1:0
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
b b16 Plain p186:45:14:1:0 0 0 - - b13:0 b6:1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b16:0,b18:0
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b16,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b6:b1,b14:b6,b16:b6,b5:b1,b9:b5,b12:b9,b11:b9,b10:b5,b2:b1,b13:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:83,b6:b1:b16:b2:35:74,b14:b6:b15:b13:44:65,b16:b6:-:b14:38:41,b5:b1:b10:b6:5:32,b9:b5:b11:-:14:29,b12:b9:-:-:23:26,b11:b9:-:b12:17:20,b10:b5:-:b9:8:11,b2:b1:-:-:77:80,b13:b6:-:-:68:71,b15:b14:b18:-:47:62,b17:b15:-:-:56:59,b18:b15:-:b17:50:53
cache loopnest 19 0 b15:-:2:1:1:0 b15:0,b17:0
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
fstate laidout
dcllen 7
end
pass 51 "schedule"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 1 0 - v22 b6:0,b5:0 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b6 ARM64NZ p186:45:14:1:0 1 0 - v17 b14:0,b16:0 b1:0
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b16 Plain p186:45:14:1:0 0 0 - - b13:0 b6:1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b16:0,b18:0
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b16,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b6:b1,b14:b6,b16:b6,b5:b1,b9:b5,b12:b9,b11:b9,b10:b5,b2:b1,b13:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:83,b6:b1:b16:b2:35:74,b14:b6:b15:b13:44:65,b16:b6:-:b14:38:41,b5:b1:b10:b6:5:32,b9:b5:b11:-:14:29,b12:b9:-:-:23:26,b11:b9:-:b12:17:20,b10:b5:-:b9:8:11,b2:b1:-:-:77:80,b13:b6:-:-:68:71,b15:b14:b18:-:47:62,b17:b15:-:-:56:59,b18:b15:-:b17:50:53
cache loopnest 19 0 b15:-:2:1:1:0 b15:0,b17:0
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
fstate scheduled,laidout
dcllen 7
end
pass 52 "late nilcheck"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 1 0 - v22 b6:0,b5:0 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b6 ARM64NZ p186:45:14:1:0 1 0 - v17 b14:0,b16:0 b1:0
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b16 Plain p186:45:14:1:0 0 0 - - b13:0 b6:1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b16:0,b18:0
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b16,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b6:b1,b14:b6,b16:b6,b5:b1,b9:b5,b12:b9,b11:b9,b10:b5,b2:b1,b13:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:83,b6:b1:b16:b2:35:74,b14:b6:b15:b13:44:65,b16:b6:-:b14:38:41,b5:b1:b10:b6:5:32,b9:b5:b11:-:14:29,b12:b9:-:-:23:26,b11:b9:-:b12:17:20,b10:b5:-:b9:8:11,b2:b1:-:-:77:80,b13:b6:-:-:68:71,b15:b14:b18:-:47:62,b17:b15:-:-:56:59,b18:b15:-:b17:50:53
cache loopnest 19 0 b15:-:2:1:1:0 b15:0,b17:0
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
fstate scheduled,laidout
dcllen 7
end
pass 53 "flagalloc"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 1 0 - v22 b6:0,b5:0 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b6 ARM64NZ p186:45:14:1:0 1 0 - v17 b14:0,b16:0 b1:0
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v44 ARM64MOVDconst t3 -1022 - p0:0:0:0:0 1 -
v v48 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
b b16 Plain p186:45:14:1:0 0 0 - - b13:0 b6:1
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
v v28 ARM64MOVDconst t4 1 - p0:0:0:0:0 2 -
v v21 ARM64MOVDconst t3 2047 - p0:0:0:0:0 2 -
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v15,v17,v21,v13,v28,v1
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v15,v11,v21,v28,v13,v1
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v74,v59
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v15,v61,v62,v13,v13,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b16:0,b18:0
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
v v74 Phi t3 0 - p186:45:3:0:0 1 v12,v67
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v44,v54
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v48
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v31,v27,v30,v42,v25,v39,v23,v19,v58,v52,v50,v47,v18,v16,v14,v33,v68,v70,v72,v76,v43,v69,v71,v73,v77,v49,v53,v45,v38,v37,v36,v35,v57,v55,v26,v41,v24,v65,v64,v63,v60,v20,v9,v8,v7,v6,v5,v4,v3,v2
freeb b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b16,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b6:b1,b14:b6,b16:b6,b5:b1,b9:b5,b12:b9,b11:b9,b10:b5,b2:b1,b13:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:83,b6:b1:b16:b2:35:74,b14:b6:b15:b13:44:65,b16:b6:-:b14:38:41,b5:b1:b10:b6:5:32,b9:b5:b11:-:14:29,b12:b9:-:-:23:26,b11:b9:-:b12:17:20,b10:b5:-:b9:8:11,b2:b1:-:-:77:80,b13:b6:-:-:68:71,b15:b14:b18:-:47:62,b17:b15:-:-:56:59,b18:b15:-:b17:50:53
cache loopnest 19 0 b15:-:2:1:1:0 b15:0,b17:0
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
fstate scheduled,laidout
dcllen 7
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.funpack64}" a2 1 1 5 8 8 1 5
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
abiparam out 1 t2 a5 1 -1
abiparam out 2 t3 a6 2 -1
abiparam out 3 t4 a7 3 -1
abiparam out 4 t4 a8 4 -1
callreg 0:1,1:2,2:4,3:8,4:10 - 0 -
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 1 0 - v22 b6:0,b5:0 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b6 ARM64NZ p186:45:14:1:0 1 0 - v17 b14:0,b16:0 b1:0
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v31 ARM64MOVDconst t3 -1022 - p186:47:4:2:0 1 -
b b16 Plain p186:45:14:1:0 0 0 - - b13:0 b6:1
v v33 Copy t3 0 - p186:45:3:2:0 1 v12
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v27 Copy t2 0 - p186:38:4:2:0 1 v15
v v30 ARM64MOVDconst t3 2047 - p186:38:4:2:0 1 -
v v42 Copy t4 0 - p186:38:4:2:0 1 v13
v v25 ARM64MOVDconst t4 1 - p186:38:4:2:0 1 -
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v27,v17,v30,v42,v25,v1
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v39 Copy t2 0 - p186:41:3:2:0 1 v15
v v23 Copy t2 0 - p186:41:3:2:0 1 v11
v v19 ARM64MOVDconst t3 2047 - p186:41:3:2:0 1 -
v v58 ARM64MOVDconst t4 1 - p186:41:3:2:0 1 -
v v52 Copy t4 0 - p186:41:3:2:0 1 v13
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v39,v23,v19,v58,v52,v1
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v14,v59
v v50 Copy t2 0 - p186:58:2:2:0 1 v15
v v47 Copy t4 0 - p186:58:2:2:0 1 v13
v v18 Copy t4 0 - p186:58:2:2:0 1 v13
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v50,v61,v62,v47,v18,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b16:0,b18:0
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
v v74 Phi t3 0 - p186:45:3:0:0 1 v33,v68
v v14 Copy t3 0 - p186:58:2:2:0 1 v74
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v31,v54
v v16 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v16
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
v v68 Copy t3 0 - p186:45:3:2:0 1 v67
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v6,v7,v8,v9,v20,v24,v26,v35,v36,v37,v38,v41,v43,v45,v49,v53,v55,v57,v60,v63,v64,v65,v69,v70,v71,v72,v73,v76,v77
freeb b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b16,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b6:b1,b14:b6,b16:b6,b5:b1,b9:b5,b12:b9,b11:b9,b10:b5,b2:b1,b13:b6,b15:b14,b17:b15,b18:b15
cache sdom b1:-:b5:-:2:83,b6:b1:b16:b2:35:74,b14:b6:b15:b13:44:65,b16:b6:-:b14:38:41,b5:b1:b10:b6:5:32,b9:b5:b11:-:14:29,b12:b9:-:-:23:26,b11:b9:-:b12:17:20,b10:b5:-:b9:8:11,b2:b1:-:-:77:80,b13:b6:-:-:68:71,b15:b14:b18:-:47:62,b17:b15:-:-:56:59,b18:b15:-:b17:50:53
cache loopnest 19 0 b15:-:2:1:1:0 b15:0,b17:0
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
fstate scheduled,laidout
regalloc 76 v10:R0,v11:ZERO,v12:ZERO,v13:ZERO,v14:R2,v15:R5,v16:R7,v17:R1,v18:R4,v19:R2,v22:R6,v23:R1,v25:R4,v27:R0,v30:R2,v31:R6,v33:R0,v34:[],v39:R0,v40:[],v42:R3,v46:R1,v47:R3,v50:R0,v51:R1,v52:R4,v54:R6,v56:R1,v58:R3,v59:R2,v61:R1,v62:R2,v66:[],v67:R6,v68:R0,v74:R0,v75:R1
dcllen 7
end
pass 55 "loop rotate"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 1 0 - v22 b6:0,b5:0 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b6 ARM64NZ p186:45:14:1:0 1 0 - v17 b14:0,b16:0 b1:0
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v31 ARM64MOVDconst t3 -1022 - p186:47:4:2:0 1 -
b b16 Plain p186:45:14:1:0 0 0 - - b13:0 b6:1
v v33 Copy t3 0 - p186:45:3:2:0 1 v12
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v27 Copy t2 0 - p186:38:4:2:0 1 v15
v v30 ARM64MOVDconst t3 2047 - p186:38:4:2:0 1 -
v v42 Copy t4 0 - p186:38:4:2:0 1 v13
v v25 ARM64MOVDconst t4 1 - p186:38:4:2:0 1 -
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v27,v17,v30,v42,v25,v1
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v39 Copy t2 0 - p186:41:3:2:0 1 v15
v v23 Copy t2 0 - p186:41:3:2:0 1 v11
v v19 ARM64MOVDconst t3 2047 - p186:41:3:2:0 1 -
v v58 ARM64MOVDconst t4 1 - p186:41:3:2:0 1 -
v v52 Copy t4 0 - p186:41:3:2:0 1 v13
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v39,v23,v19,v58,v52,v1
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v14,v59
v v50 Copy t2 0 - p186:58:2:2:0 1 v15
v v47 Copy t4 0 - p186:58:2:2:0 1 v13
v v18 Copy t4 0 - p186:58:2:2:0 1 v13
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v50,v61,v62,v47,v18,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b16:0,b18:0
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
v v74 Phi t3 0 - p186:45:3:0:0 1 v33,v68
v v14 Copy t3 0 - p186:58:2:2:0 1 v74
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v31,v54
v v16 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v16
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
v v68 Copy t3 0 - p186:45:3:2:0 1 v67
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v6,v7,v8,v9,v20,v24,v26,v35,v36,v37,v38,v41,v43,v45,v49,v53,v55,v57,v60,v63,v64,v65,v69,v70,v71,v72,v73,v76,v77
freeb b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b16,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b6:b1,b14:b6,b16:b6,b5:b1,b9:b5,b12:b9,b11:b9,b10:b5,b2:b1,b13:b6,b17:b15,b15:b14,b18:b15
cache sdom b1:-:b5:-:2:83,b6:b1:b16:b2:35:74,b14:b6:b15:b13:44:65,b16:b6:-:b14:38:41,b5:b1:b10:b6:5:32,b9:b5:b11:-:14:29,b12:b9:-:-:23:26,b11:b9:-:b12:17:20,b10:b5:-:b9:8:11,b2:b1:-:-:77:80,b13:b6:-:-:68:71,b17:b15:-:-:56:59,b15:b14:b18:-:47:62,b18:b15:-:b17:50:53
cache loopnest 19 0 b15:-:2:1:1:0 b15:0,b17:0
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
hotness b17:3
fstate scheduled,laidout
regalloc 76 v10:R0,v11:ZERO,v12:ZERO,v13:ZERO,v14:R2,v15:R5,v16:R7,v17:R1,v18:R4,v19:R2,v22:R6,v23:R1,v25:R4,v27:R0,v30:R2,v31:R6,v33:R0,v34:[],v39:R0,v40:[],v42:R3,v46:R1,v47:R3,v50:R0,v51:R1,v52:R4,v54:R6,v56:R1,v58:R3,v59:R2,v61:R1,v62:R2,v66:[],v67:R6,v68:R0,v74:R0,v75:R1
dcllen 7
end
pass 56 "trim"
f b1 t1 a1 77 18
b b1 ARM64Z p186:43:7:1:0 1 0 - v22 b6:0,b5:0 -
v v10 ArgIntReg t2 0 a9 p186:43:7:0:0 3 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v13 ARM64ZERO t4 0 - p0:0:0:0:0 4 -
v v15 ARM64ANDconst t2 -9223372036854775808 - p186:30:11:1:0 3 v10
v v17 ARM64ANDconst t2 4503599627370495 - p186:31:11:1:0 6 v10
v v22 ARM64UBFX t3 13323 - p186:32:27:1:0 3 v10
b b6 ARM64NZ p186:45:14:1:0 1 0 - v17 b14:0,b16:0 b1:0
v v12 ARM64ZERO t3 0 - p0:0:0:0:0 1 -
b b14 Plain p186:47:4:1:0 0 0 - - b15:0 b6:0
v v31 ARM64MOVDconst t3 -1022 - p186:47:4:2:0 1 -
b b16 Plain p186:45:14:1:0 0 0 - - b13:0 b6:1
v v33 Copy t3 0 - p186:45:3:2:0 1 v12
b b5 ARM64EQ p186:35:20:0:0 0 0 - v29 b9:0,b10:0 b1:1
v v29 ARM64CMPconst t29 2047 - p186:35:2:1:0 1 v22
b b9 ARM64NZ p186:36:14:1:0 0 0 - v17 b12:0,b11:0 b5:0
b b12 Ret p186:38:4:1:0 0 0 - v34 - b9:0
v v27 Copy t2 0 - p186:38:4:2:0 1 v15
v v30 ARM64MOVDconst t3 2047 - p186:38:4:2:0 1 -
v v42 Copy t4 0 - p186:38:4:2:0 1 v13
v v25 ARM64MOVDconst t4 1 - p186:38:4:2:0 1 -
v v34 MakeResult t35 0 - p186:38:4:1:0 1 v27,v17,v30,v42,v25,v1
b b11 Ret p186:41:3:1:0 0 0 - v40 - b9:1
v v11 ARM64ZERO t2 0 - p0:0:0:0:0 1 -
v v39 Copy t2 0 - p186:41:3:2:0 1 v15
v v23 Copy t2 0 - p186:41:3:2:0 1 v11
v v19 ARM64MOVDconst t3 2047 - p186:41:3:2:0 1 -
v v58 ARM64MOVDconst t4 1 - p186:41:3:2:0 1 -
v v52 Copy t4 0 - p186:41:3:2:0 1 v13
v v40 MakeResult t35 0 - p186:41:3:1:0 1 v39,v23,v19,v58,v52,v1
b b10 Plain p186:56:7:1:0 0 0 - - b2:1 b5:1
v v56 ARM64ORconst t2 4503599627370496 - p186:55:8:1:0 1 v17
v v59 ARM64SUBconst t3 1023 - p186:56:7:1:0 1 v22
b b2 Ret p186:58:2:1:0 0 0 - v66 - b13:0,b10:0
v v61 Phi t2 0 - p186:58:2:0:0 1 v75,v56
v v62 Phi t3 0 - p186:58:2:0:0 1 v14,v59
v v50 Copy t2 0 - p186:58:2:2:0 1 v15
v v47 Copy t4 0 - p186:58:2:2:0 1 v13
v v18 Copy t4 0 - p186:58:2:2:0 1 v13
v v66 MakeResult t35 0 - p186:58:2:1:0 1 v50,v61,v62,v47,v18,v1
b b13 Plain p186:45:3:1:0 0 0 - - b2:0 b16:0,b18:0
v v75 Phi t2 0 - p186:45:3:0:0 1 v17,v46
v v74 Phi t3 0 - p186:45:3:0:0 1 v33,v68
v v14 Copy t3 0 - p186:58:2:2:0 1 v74
b b17 Plain p186:47:16:1:0 0 0 - - b15:1 b15:0
v v51 ARM64ADD t2 0 - p186:48:10:1:0 1 v46,v46
v v54 ARM64SUBconst t3 1 - p186:49:8:1:0 1 v67
b b15 ARM64ULT p186:47:16:0:0 1 0 - v32 b17:0,b18:0 b14:0,b17:0
v v46 Phi t2 0 - p186:47:13:0:0 4 v17,v51
v v67 Phi t3 0 - p186:47:13:0:0 2 v31,v54
v v16 ARM64MOVDconst t2 4503599627370496 - p186:47:13:1:0 1 -
v v32 ARM64CMP t29 0 - p186:47:13:1:0 1 v46,v16
b b18 Plain p186:45:3:1:0 0 0 - - b13:1 b15:1
v v68 Copy t3 0 - p186:45:3:2:0 1 v67
names s1
named s1 v10
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v6,v7,v8,v9,v20,v24,v26,v35,v36,v37,v38,v41,v43,v45,v49,v53,v55,v57,v60,v63,v64,v65,v69,v70,v71,v72,v73,v76,v77
freeb b8,b7,b4,b3
cache postorder b17,b2,b13,b18,b15,b14,b16,b6,b12,b11,b9,b10,b5,b1
cache idom b1:-,b6:b1,b14:b6,b16:b6,b5:b1,b9:b5,b12:b9,b11:b9,b10:b5,b2:b1,b13:b6,b17:b15,b15:b14,b18:b15
cache sdom b1:-:b5:-:2:83,b6:b1:b16:b2:35:74,b14:b6:b15:b13:44:65,b16:b6:-:b14:38:41,b5:b1:b10:b6:5:32,b9:b5:b11:-:14:29,b12:b9:-:-:23:26,b11:b9:-:b12:17:20,b10:b5:-:b9:8:11,b2:b1:-:-:77:80,b13:b6:-:-:68:71,b17:b15:-:-:56:59,b15:b14:b18:-:47:62,b18:b15:-:b17:50:53
cache loopnest 19 0 b15:-:2:1:1:0 b15:0,b17:0
cache auxmap a3:1,-:2,a9:3
cache linestarts 186:30:58
hotness b17:3
fstate scheduled,laidout
regalloc 76 v10:R0,v11:ZERO,v12:ZERO,v13:ZERO,v14:R2,v15:R5,v16:R7,v17:R1,v18:R4,v19:R2,v22:R6,v23:R1,v25:R4,v27:R0,v30:R2,v31:R6,v33:R0,v34:[],v39:R0,v40:[],v42:R3,v46:R1,v47:R3,v50:R0,v51:R1,v52:R4,v54:R6,v56:R1,v58:R3,v59:R2,v61:R1,v62:R2,v66:[],v67:R6,v68:R0,v74:R0,v75:R1
dcllen 7
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t21,t24,t25,t26,t27
typelink t28=t32
typeorder t5,t9,t6,t10,t7,t11,t8,t2,t3,t14,t15,t25,t26,t12,t13,t4,t17,t18,t19,t33,t20,t21,t22,t23,t34,t24,t1,t16,t27,t28,t30,t29,t31,t32,t35
eof
"#

/-- `std/std/runtime/funpack64,1.prog` (quick-v10). -/
def fProgK : String := r#"gofv-prog 3
pkg "runtime"
func "funpack64" 1
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
type t1 8 8 0 0 - "uint64"
name n1 "f" PPARAM t1 1 "runtime.f" 0 a3
name n2 "sign" PPARAMOUT t1 1 "runtime.sign" 0 a4
name n3 "mant" PPARAMOUT t1 1 "runtime.mant" 0 a5
type t2 8 8 0 0 - "int"
name n4 "exp" PPARAMOUT t2 1 "runtime.exp" 0 a6
type t3 1 1 0 0 - "bool"
name n5 "inf" PPARAMOUT t3 1 "runtime.inf" 0 a7
name n6 "nan" PPARAMOUT t3 1 "runtime.nan" 0 a8
name n7 ".autotmp_6" PAUTO t2 3 "runtime..autotmp_6" 0 -
in n1 0 used
in n2 0 used,outregs
in n3 0 used,outregs
in n4 0 used,outregs
in n5 0 used,outregs
in n6 0 used,outregs
in n7 0 used,autotmp
out n1 0 used
opt n7 0 autotmp
opt n4 0 outregs
opt n3 0 outregs
opt n2 0 outregs
opt n5 0 outregs
opt n6 0 outregs
stack 0 0 8
end
genin
posbase p186 "runtime/softfloat64.go" 1 1 -1 183 "runtime/softfloat64.go" "runtime/softfloat64.go" 1 1
sym y1 "runtime.funpack64" 1
curfn p186:29:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 29 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.funpack64.arginfo1" 0
sym y4 "runtime.funpack64.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p186:29:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p186:29:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p186:29:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p186:29:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p186:29:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p186:29:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p186:30:11:1:0
p 7 7 0 0 0 - AND 0 CONST/0/0/0/NONE/0/-9223372036854775808/-/- 8192 - REG/8197/0/0/NONE/0/0/-/- 0 0 p186:30:11:1:0
p 8 8 0 0 0 - AND 0 CONST/0/0/0/NONE/0/4503599627370495/-/- 8192 - REG/8193/0/0/NONE/0/0/-/- 0 0 p186:31:11:1:0
p 9 9 0 0 0 - UBFX 0 CONST/0/0/0/NONE/0/52/-/- 8192 0:CONST/0/0/0/NONE/0/11/-/- REG/8198/0/0/NONE/0/0/-/- 0 0 p186:32:27:1:0
p 10 10 0 0 0 - CBNZ 0 REG/8198/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@16 0 0 p186:43:7:1:0
p 11 11 0 0 0 - CBZ 0 REG/8193/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@14 0 0 p186:45:14:1:0
p 12 12 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/-1022/-/- 0 - REG/8198/0/0/NONE/0/0/-/- 0 0 p186:47:4:1:0
p 13 13 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@40 0 0 p186:47:4:2:0
p 14 14 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p186:45:3:1:0
p 15 15 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@36 0 0 p186:45:14:2:0
p 16 16 0 0 0 - CMP 0 CONST/0/0/0/NONE/0/2047/-/- 8198 - _ 0 0 p186:35:2:1:0
p 17 17 0 0 0 - BNE 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@30 0 0 p186:35:20:2:0
p 18 18 0 0 0 - CBZ 0 REG/8193/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@24 0 0 p186:36:14:1:0
p 19 19 0 0 0 - MOVD 0 REG/8197/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p186:38:4:1:0
p 20 20 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/2047/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p186:38:4:2:0
p 21 21 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p186:38:4:2:0
p 22 22 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/1/-/- 0 - REG/8196/0/0/NONE/0/0/-/- 0 0 p186:38:4:2:0
p 23 23 0 0 0 - RET 0 _ 0 - _ 0 0 p186:38:4:2:0
p 24 24 0 0 0 - MOVD 0 REG/8197/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p186:41:3:1:0
p 25 25 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p186:41:3:2:0
p 26 26 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/2047/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p186:41:3:2:0
p 27 27 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/1/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p186:41:3:2:0
p 28 28 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8196/0/0/NONE/0/0/-/- 0 0 p186:41:3:2:0
p 29 29 0 0 0 - RET 0 _ 0 - _ 0 0 p186:41:3:2:0
p 30 30 0 0 0 - ORR 0 CONST/0/0/0/NONE/0/4503599627370496/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p186:55:8:1:0
p 31 31 0 0 0 - SUB 0 CONST/0/0/0/NONE/0/1023/-/- 8198 - REG/8194/0/0/NONE/0/0/-/- 0 0 p186:56:7:1:0
p 32 32 0 0 0 - MOVD 0 REG/8197/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p186:58:2:1:0
p 33 33 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p186:58:2:2:0
p 34 34 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8196/0/0/NONE/0/0/-/- 0 0 p186:58:2:2:0
p 35 35 0 0 0 - RET 0 _ 0 - _ 0 0 p186:58:2:2:0
p 36 36 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p186:58:2:2:0
p 37 37 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@32 0 0 p186:45:3:1:0
p 38 38 0 0 0 - ADD 0 REG/8193/0/0/NONE/0/0/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p186:48:10:1:0
p 39 39 0 0 0 - SUB 0 CONST/0/0/0/NONE/0/1/-/- 8198 - REG/8198/0/0/NONE/0/0/-/- 0 0 p186:49:8:1:0
p 40 40 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/4503599627370496/-/- 0 - REG/8199/0/0/NONE/0/0/-/- 0 0 p186:47:13:1:0
p 41 41 0 0 0 - CMP 0 REG/8199/0/0/NONE/0/0/-/- 8193 - _ 0 0 p186:47:13:2:0
p 42 42 0 0 0 - BLO 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@38 0 0 p186:47:16:2:0
p 43 43 0 0 0 - MOVD 0 REG/8198/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p186:45:3:1:0
p 44 44 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@36 0 0 p186:45:3:2:0
p 45 45 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 29 201080
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
dbgloc 0 1:-10000:16:33:50
dbgregout n2,n3,n4,n5,n6
dbgpc 16:33:15
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p186:29:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p186:29:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p186:29:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p186:29:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p186:29:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p186:29:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p186:30:11:1:0
p 7 0 0 0 53 - AND 0 CONST/0/0/0/NONE/22/-9223372036854775808/-/- 8192 - REG/8197/0/0/NONE/2/0/-/- 0 0 p186:30:11:1:0
p 8 4 0 0 53 - AND 0 CONST/0/0/0/NONE/22/4503599627370495/-/- 8192 - REG/8193/0/0/NONE/2/0/-/- 0 0 p186:31:11:1:0
p 9 8 0 0 81 - UBFX 0 CONST/0/0/0/NONE/18/52/-/- 8192 0:CONST/0/0/0/NONE/18/11/-/- REG/8198/0/0/NONE/2/0/-/- 0 0 p186:32:27:1:0
p 10 12 0 0 85 - CBNZ 0 REG/8198/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/16/-/@16 0 0 p186:43:7:1:0
p 11 16 0 0 85 - CBZ 0 REG/8193/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/14/-/@14 0 0 p186:45:14:1:0
p 12 20 0 0 318 - MOVD 0 CONST/0/0/0/NONE/23/-1022/-/- 0 - REG/8198/0/0/NONE/2/0/-/- 0 0 p186:47:4:1:0
p 13 24 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/40/-/@40 0 0 p186:47:4:2:0
p 14 28 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p186:45:3:1:0
p 15 32 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/36/-/@36 0 0 p186:45:14:2:0
p 16 36 0 0 96 - CMP 0 CONST/0/0/0/NONE/17/2047/-/- 8198 - NONE/0/0/0/NONE/1/0/-/- 0 0 p186:35:2:1:0
p 17 40 0 0 80 - BNE 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/30/-/@30 0 0 p186:35:20:2:0
p 18 44 0 0 85 - CBZ 0 REG/8193/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/24/-/@24 0 0 p186:36:14:1:0
p 19 48 0 0 301 - MOVD 0 REG/8197/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p186:38:4:1:0
p 20 52 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/2047/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p186:38:4:2:0
p 21 56 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p186:38:4:2:0
p 22 60 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/1/-/- 0 - REG/8196/0/0/NONE/2/0/-/- 0 0 p186:38:4:2:0
p 23 64 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p186:38:4:2:0
p 24 68 0 0 301 - MOVD 0 REG/8197/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p186:41:3:1:0
p 25 72 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p186:41:3:2:0
p 26 76 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/2047/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p186:41:3:2:0
p 27 80 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/1/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p186:41:3:2:0
p 28 84 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8196/0/0/NONE/2/0/-/- 0 0 p186:41:3:2:0
p 29 88 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p186:41:3:2:0
p 30 92 0 0 53 - ORR 0 CONST/0/0/0/NONE/22/4503599627370496/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p186:55:8:1:0
p 31 96 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/1023/-/- 8198 - REG/8194/0/0/NONE/2/0/-/- 0 0 p186:56:7:1:0
p 32 100 0 0 301 - MOVD 0 REG/8197/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p186:58:2:1:0
p 33 104 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p186:58:2:2:0
p 34 108 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8196/0/0/NONE/2/0/-/- 0 0 p186:58:2:2:0
p 35 112 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p186:58:2:2:0
p 36 116 0 0 301 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p186:58:2:2:0
p 37 120 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/32/-/@32 0 0 p186:45:3:1:0
p 38 124 0 0 23 - ADD 0 REG/8193/0/0/NONE/2/0/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p186:48:10:1:0
p 39 128 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/1/-/- 8198 - REG/8198/0/0/NONE/2/0/-/- 0 0 p186:49:8:1:0
p 40 132 0 0 317 - MOVD 0 CONST/0/0/0/NONE/22/4503599627370496/-/- 0 - REG/8199/0/0/NONE/2/0/-/- 0 0 p186:47:13:1:0
p 41 136 0 0 92 - CMP 0 REG/8199/0/0/NONE/2/0/-/- 8193 - NONE/0/0/0/NONE/1/0/-/- 0 0 p186:47:13:2:0
p 42 140 0 0 80 - BLO 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/38/-/@38 0 0 p186:47:16:2:0
p 43 144 0 0 301 - MOVD 0 REG/8198/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p186:45:3:1:0
p 44 148 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/36/-/@36 0 0 p186:45:3:2:0
fn y1 8 0 0 0 29 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 160 0 0500419201cc409206f874d3c60000b5610000b4a67f80921b000014e0031faa15000014dffc1ff1a1010054c10000b4e00305aae22b40b2e3031faae40340b2c0035fd6e00305aae1031faae22b40b2e30340b2e4031faac0035fd621004cb2c2fc0fd1e00305aae3031faae4031faac0035fd6e20300aafbffff172100018bc60400d10702e0d23f0007eb83ffff54e00306aaf8ffff170000000000000000 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 183
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 3 1 28000 012800 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 042800 0
data y9 SRODATA 3 1 28000 022800 0
data y10 SRODATA 4 1 28000 f0022800 0
data y11 SRODATA 39 1 28000 3e0102010201160104010402030213020201040506061c01020104051901060102010303030400 0
data y12 SRODATA 3 1 28000 002800 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "go:info.runtime.funpack64$abstract" 0
sym y17 "" 0
sym y18 "go:info.uint64" 0
sym y19 "go:info.int" 0
sym y20 "go:info.bool" 0
sym y21 "type:bool" 0
sym y22 "type:int" 0
sym y23 "type:uint64" 0
dwfn y13 y14 y15 y16 y17 "runtime.funpack64" 183:29 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2,n3,n4,n5,n6
dwprecursor y1 y16 n1,n2,n3,n4,n5,n6
dwname n1 1 1 0 0 0 0 0 0 - - "uint64" 0 0 1 p186:29:16:0:0
dwname n7 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p186:34:2:0:0
dwname n4 1 0 0 0 0 0 0 1 - - "int" 0 0 1 p186:29:46:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "uint64" 0 0 1 p186:29:33:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uint64" 0 0 1 p186:29:27:0:0
dwname n5 1 0 0 0 0 0 0 1 - - "bool" 0 0 1 p186:29:55:0:0
dwname n6 1 0 0 0 0 0 0 1 - - "bool" 0 0 1 p186:29:60:0:0
var 0 0 "f" 5 1 0 0 0 8 y18 "runtime/softfloat64.go" 29 16 0 0 1 0 v0
var 1 0 "sign" 5 1 1 0 0 0 y18 "runtime/softfloat64.go" 29 27 0 1 1 0 -
var 2 0 "mant" 5 1 1 0 0 0 y18 "runtime/softfloat64.go" 29 33 0 2 1 0 -
var 3 0 "exp" 5 1 1 0 0 0 y19 "runtime/softfloat64.go" 29 46 0 3 1 0 -
var 4 0 "inf" 5 1 1 0 0 0 y20 "runtime/softfloat64.go" 29 55 0 4 1 0 -
var 5 0 "nan" 5 1 1 0 0 0 y20 "runtime/softfloat64.go" 29 60 0 5 1 0 -
scope 0 0 - 0,1,2,3,4,5
dieref y13 5 y16 0
dieref y13 7 y16 1
dieref y13 8 y16 2
dieref y13 9 y16 3
dieref y13 10 y16 4
dieref y13 11 y16 5
dieoff y16 0:22,1:30,2:41,3:52,4:62,5:72
data y13 SDWARFFCN 51 0 0 06000000000000a001019c2900000000000000002a00000000002a00000000002a00000000002a00000000002a000000000000 12
reloc 0 0 R_USETYPE 0 y21
reloc 0 0 R_USETYPE 0 y22
reloc 0 0 R_USETYPE 0 y23
reloc 1 4 R_DWARFSECREF 0 y16
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 12 4 R_DWARFSECREF 0 y16
reloc 16 4 R_DWARFSECREF 0 y14
reloc 21 4 R_DWARFSECREF 0 y16
reloc 27 4 R_DWARFSECREF 0 y16
reloc 33 4 R_DWARFSECREF 0 y16
reloc 39 4 R_DWARFSECREF 0 y16
reloc 45 4 R_DWARFSECREF 0 y16
data y14 SDWARFLOC 9 0 0 010000040020015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 71 0 0 000902000000000000000004b801031814383803063c393906370635063706037a330637063839063706b20637060309dc38390637060377ab3a38350637065d0637020c000101 1
reloc 3 8 R_ADDR 0 y1
data y16 SDWARFABSFCN 83 0 1 0572756e74696d652e66756e7061636b363400011d012266000000000000227369676e000100000000226d616e740001000000002265787000010000000022696e66000100000000226e616e00010000000000 6
reloc 26 4 R_DWARFSECREF 0 y18
reloc 37 4 R_DWARFSECREF 0 y18
reloc 48 4 R_DWARFSECREF 0 y18
reloc 58 4 R_DWARFSECREF 0 y19
reloc 68 4 R_DWARFSECREF 0 y20
reloc 78 4 R_DWARFSECREF 0 y20
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stInK : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsaK fProgK

def lcK : LocCtx :=
  match stInK with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

def psK : Array GoFV.Asm.Prog :=
  match stInK with
  | .ok x => x.2.1
  | .error _ => #[]

def bsK : ID → Option Nat :=
  match stInK with
  | .ok x => x.2.2.1
  | .error _ => fun _ => none

def gK : G2In :=
  match stInK with
  | .ok x => x.2.2.2
  | .error _ => { syms := #[], slotOp := fun _ => none, stksize := 0 }

/-- The PC table `checkG32` gives (one row per block: an entry per value, then the
terminator). -/
def tabK : PcTab := [(1, [5, 5, 5, 5, 8, 9, 10]), (6, [11, 11]), (14, [12, 13]), (16, [14, 15]),
  (5, [16, 17]), (9, [18]), (12, [19, 20, 21, 22, 23, 23]), (11, [24, 24, 25, 26, 27, 28, 29, 29]),
  (10, [30, 31, 32]), (2, [32, 32, 32, 33, 34, 35, 35]), (13, [36, 36, 36, 37]), (17, [38, 39, 40]),
  (15, [40, 40, 40, 41, 42]), (18, [43, 44])]

/-- The class table `checkG32` gives. -/
def ktK : KTab := (match checkG32 lcK psK bsK gK with
  | .ok (_, k) => k
  | .error _ => [])

def blk10 : Block := (lcK.ctx.f.block? 10).getD default

def valK (n : ID) : Value := (lcK.ctx.f.value? n).getD default

def LK : Link := Lof psK

def EK : MatchEnv := Eof lcK psK tabK

/-- The mantissa `mant = f & (1 << 52 - 1)` (`v17`). -/
def mant : BitVec 64 := 0x123456789abcd

/-- The `runLoc` state before `v56`: `mant` in `R1`, every other register `poison`. -/
def s0K : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 1 then .int .w64 mant else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v56`: `X1 = mant`, the activation's `g` and `FP`, the PC of `v56`, a zero
memory. -/
def m0K : MState :=
  { x := fun k => if k = 1 then mant else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := EK.pcOf 10 0, mem := fun _ => 0 }

/-- The register holds the 64-bit integer `mant ||| 1 << 52`. -/
def isResK : Option Val → Bool
  | some (.int .w64 x) => x == mant ||| 0x10000000000000
  | _ => false

theorem isResK_spec {o : Option Val} (h : isResK o = true) :
    o = some (.int .w64 (mant ||| 0x10000000000000)) := by
  unfold isResK at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on `funpack64`: it holds an arm64 op, `checkG32` accepts it
with `tabK` and `ktK` and `checkG30` does not; it accesses no frame variable and has no home slot;
`b10` holds `v56` (`ORconst [1 << 52]`) at index 0, `R1` has class 64 before `v56` and the
upper-bit table is empty there; `stepLoc` runs `v56` from `s0K` to `R1 = mant ||| 1 << 52`. -/
def gFactsK : Bool :=
  lcK.ctx.f.lowered &&
    (checkG32 lcK psK bsK gK).toOption == some (tabK, ktK) &&
    (checkG30 lcK psK bsK gK).toOption.isNone &&
    (accessedVars lcK).isEmpty && (homeSlots lcK).isEmpty &&
    lcK.ctx.f.blocks.toList.contains 10 && (lcK.ctx.f.block? 10).isSome &&
    (lcK.ctx.f.value? 56).isSome && blk10.values[0]? == some 56 &&
    (valK 56).op == .ARM64ORconst && (kAt lcK ktK 10 blk10 0).get 1 == some 64 &&
    uL lcK blk10 0 == [] &&
    GenG1.okThen (stepLoc GenG2.env lcK s0K (valK 56)) fun s1 => isResK s1.regs[1]?

/-! ## The facts -/

/-- What compiled evaluation checks: `gFactsOr` and `gFactsK`. -/
def gFacts : Bool := gFactsOr && gFactsK

theorem g32_facts : gFacts = true := by
  native_decide

/-- The facts of `gFactsOr` as hypotheses. -/
theorem factsOr :
    lc.ctx.f.lowered = true ∧ checkG32 lc ps bs g = .ok (tab, kt) ∧
      (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 1 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 1 = some blk1 ∧ lc.ctx.f.value? 9 = some (val 9) ∧
      blk1.values[3]? = some 9 ∧ (val 9).op = .ARM64OR ∧
      (kAt lc kt 1 blk1 3).get 0 = some 64 ∧ (kAt lc kt 1 blk1 3).get 1 = some 64 ∧
      uL lc blk1 3 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 9)) (fun s1 => isRes s1.regs[0]?) = true := by
  have hf := g32_facts
  simp only [gFacts, Bool.and_eq_true] at hf
  have hf := hf.1
  simp only [gFactsOr, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hres⟩, -⟩, hav⟩, hsl⟩, hm1⟩, hb1s⟩, hv9s⟩, hi3⟩, hop⟩, hk0⟩, hk1⟩,
    hu⟩, hrun⟩ := hf
  refine ⟨hl, ?_, hav, hsl, hm1, ?_, ?_, hi3, hop, hk0, hk1, hu, hrun⟩
  · revert hres; cases checkG32 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [blk1, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv9s
    simp [val, hv]

/-- The facts of `gFactsK` as hypotheses. -/
theorem factsK :
    lcK.ctx.f.lowered = true ∧ checkG32 lcK psK bsK gK = .ok (tabK, ktK) ∧
      (accessedVars lcK).isEmpty = true ∧
      (homeSlots lcK).isEmpty = true ∧ 10 ∈ lcK.ctx.f.blocks.toList ∧
      lcK.ctx.f.block? 10 = some blk10 ∧ lcK.ctx.f.value? 56 = some (valK 56) ∧
      blk10.values[0]? = some 56 ∧ (valK 56).op = .ARM64ORconst ∧
      (kAt lcK ktK 10 blk10 0).get 1 = some 64 ∧ uL lcK blk10 0 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lcK s0K (valK 56)) (fun s1 => isResK s1.regs[1]?) =
        true := by
  have hf := g32_facts
  simp only [gFacts, Bool.and_eq_true] at hf
  have hf := hf.2
  simp only [gFactsK, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hres⟩, -⟩, hav⟩, hsl⟩, hm10⟩, hb10s⟩, hv56s⟩, hi0⟩, hop⟩, hk1⟩, hu⟩,
    hrun⟩ := hf
  refine ⟨hl, ?_, hav, hsl, hm10, ?_, ?_, hi0, hop, hk1, hu, hrun⟩
  · revert hres; cases checkG32 lcK psK bsK gK <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb10s
    simp [blk10, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv56s
    simp [valK, hv]

/-! ## `OR` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w64 0x1234) ∨ (r = 1 ∧ x = .int .w64 c64a) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · split at h
      · rename_i h1; exact Or.inr (Or.inl ⟨h1, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatch0 : LocMatch E s0 1 3 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl rfl
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E, Eof]; decide,
    by simp only [MState.word, readMem, m0, E, Eof]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g32Inv0 (h0 : (kAt lc kt 1 blk1 3).get 0 = some 64)
    (h1 : (kAt lc kt 1 blk1 3).get 1 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk1 3) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · rw [h1] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v9`, the `OR`: none apply. -/
theorem pre9 {s : LocState} (hop : (val 9).op = .ARM64OR) : G14Pre lc s (val 9) := by
  have hne : ∀ o : Op, o ≠ .ARM64OR → (val 9).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G32's register op on `or64`**: from the state before `v9` with `x = 0x1234` in `R0`
(`X0 = 0x1234`) and `c64a` in `R1` (`X1 = c64a`), `g32_value` runs `ORR R1, R0, R0` (`v9`):
`runLoc`'s `R0` holds `0x1234 ||| c64a` and the machine state, related to it before `v10` under
an activation extending `E` that is again a `G28Env`, has `X0 = 0x1234 ||| 0xaa00dd55000066`. -/
theorem genG32_bin_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 9) = .ok s1 ∧
      s1.regs[0]? = some (.int .w64 (0x1234 ||| c64a)) ∧
      E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E1 s1 1 4 m1 ∧ m1.x 0 = 0x1234 ||| 0xaa00dd55000066 := by
  obtain ⟨hl, hc, hav, hsl, hm1, hb, hv9, hi3, hop, hk0, hk1, hu, hrun⟩ := factsOr
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hr1' := isRes_spec hr1
  have hE : G28Env lc g L ps 0 tab E := envOf hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64OR → (val 9).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g32_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm1 hb hi3 hv9 (by rw [hop]; rfl) locMatch0 (g32Inv0 hk0 hk1)
    (by rw [hu]; intro e he; cases he) (pre9 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  exact ⟨s1, E1, m1, hs1, hr1', hx1, hE1, hp1, hm1',
    valRel_i64 hA ((hm1'.regs 0 _ hr1').1 0 rfl)⟩

/-! ## `ORconst` -/

theorem s0K_regs {r : Nat} {x : Val} (h : s0K.regs[r]? = some x) :
    (r = 1 ∧ x = .int .w64 mant) ∨ x = .poison := by
  simp only [s0K, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0K : LocMatch EK s0K 10 0 m0K where
  regs := by
    intro r v hv
    rcases s0K_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl rfl
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0K] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0K, EK, Eof]; decide,
    by simp only [MState.word, readMem, m0K, EK, Eof]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g32Inv0K (h1 : (kAt lcK ktK 10 blk10 0).get 1 = some 64) :
    G3Inv EK lcK (kAt lcK ktK 10 blk10 0) s0K where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0K_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h1] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0K] at h

/-- The per-value premises of `v56`, the `ORconst`: none apply. -/
theorem pre56 {s : LocState} (hop : (valK 56).op = .ARM64ORconst) : G14Pre lcK s (valK 56) := by
  have hne : ∀ o : Op, o ≠ .ARM64ORconst → (valK 56).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G32's constant op on `runtime.funpack64`**: from the state before `v56` with the mantissa
`0x123456789abcd` in `R1` (`X1 = 0x123456789abcd`), `g32_value` runs
`ORR $0x10000000000000, R1, R1` (`v56`, `mant |= 1 << mantbits64`): `runLoc`'s `R1` holds
`mant ||| 1 << 52` and the machine state, related to it before `v59` under an activation extending
`EK` that is again a `G28Env`, has `X1 = 0x123456789abcd ||| 0x10000000000000`. -/
theorem genG32_binK_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lcK s0K (valK 56) = .ok s1 ∧
      s1.regs[1]? = some (.int .w64 (mant ||| 0x10000000000000)) ∧
      EK.Extends E1 ∧ G28Env lcK gK LK psK 0 tabK E1 ∧ PStar GenG2.H0 LK psK.toList 0 m0K m1 ∧
      LocMatch E1 s1 10 1 m1 ∧ m1.x 1 = 0x123456789abcd ||| 0x10000000000000 := by
  obtain ⟨hl, hc, hav, hsl, hm10, hb, hv56, hi0, hop, hk1, hu, hrun⟩ := factsK
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hr1' := isResK_spec hr1
  have hE : G28Env lcK gK LK psK 0 tabK EK := envOf hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64ORconst → (valK 56).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g32_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm10 hb hi0 hv56 (by rw [hop]; rfl) locMatch0K (g32Inv0K hk1)
    (by rw [hu]; intro e he; cases he) (pre56 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  exact ⟨s1, E1, m1, hs1, hr1', hx1, hE1, hp1, hm1',
    valRel_i64 hA ((hm1'.regs 1 _ hr1').1 1 rfl)⟩

end GoFV.Proof.Witness.GenG32
