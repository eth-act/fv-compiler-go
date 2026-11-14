import GoFV.Proof.Gen.G33
import GoFV.Proof.Witness.GenG13

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G33 of the genssa validator on `math/bits.ReverseBytes` and
`internal/bytealg.Cutover`

Two functions of the corpus `gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim:

* `std/std/math/bits/ReverseBytes,1.ssa` and `…,1.prog` (`fSsaR`, `fProgR`; `math/bits/bits.go`):

  ```go
  func ReverseBytes(x uint) uint {
  	if UintSize == 32 {
  		return uint(ReverseBytes32(uint32(x)))
  	}
  	return uint(ReverseBytes64(uint64(x)))
  }
  ```

  Block `b1`: `v6 = ArgIntReg` (`x`, `R0`), `InitMem`, `v9 = REV v6` (`REV R0, R0`), `MakeResult`,
  then the `RET`.
* `std/std/internal/bytealg/Cutover,1.ssa` and `…,1.prog` (`fSsaS`, `fProgS`;
  `internal/bytealg/index_arm64.go`, `return 4 + n>>4`). Block `b1`: `v6 = ArgIntReg` (`n`, `R0`),
  `InitMem`, `v10 = SRAconst [4] v6` (`ASR $4, R0, R1`), `v11 = ADDconst [4] v10`, `MakeResult`.

`checkG31` rejects both (`REV`, `SRAconst` are G33's ops); `checkG33` accepts them with the PC
tables `tabR`, `tabS` and the class tables `ktR`, `ktS`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g33_facts`),
`stepLoc` runs `v9` from a state with `x = 0x0102030405060708` in `R0`: `R0` then holds
`0x0807060504030201`; and `v10` from a state with `n = -256` in `R0`: `R1` then holds `-16`. On a
framed activation with `G28Env`, `g33_value` runs the `REV R0, R0` (`genG33_un_witness`: the
machine's `X0` is `0x0807060504030201`) and the `ASR $4, R0, R1` (`genG33_sra_witness`: the
machine's `X1` is `0xfffffffffffffff0`, the sign bits shifted in).
-/

namespace GoFV.Proof.Witness.GenG33

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

/-- `Eof` is a `G28Env` of a function `checkG33` accepts, with no frame variable or home slot. -/
theorem envOf {lc : LocCtx} {ps : Array GoFV.Asm.Prog} {bs : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hc : checkG33 lc ps bs g = .ok (tab, kt))
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
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ := checkG33_spec hl hc
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ := checkG33_spec hl hc
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

/-! ## `math/bits.ReverseBytes` -/

/-- `std/std/math/bits/ReverseBytes,1.ssa` (quick-v10). -/
def fSsaR : String := r#"gofv-ssa 5.1
pkg "math/bits"
func "ReverseBytes" 1 0 0
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
aux a2 sym "math/bits.ReverseBytes" "math/bits.ReverseBytes" 1 - 0 - - - - 0
posbase p2 "math/bits/bits.go" 1 1 -1
aux a3 name "x" "x" PPARAM t2 0 1 used p2:266:19:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t2 0 1 - p2:266:27:0:0
aux a1 call "AuxCall{math/bits.ReverseBytes}" a2 1 1 1 8 8 1 1
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
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Copy t11 0 - p2:270:36:2:0 1 v6
v v9 Bswap64 t11 0 - p2:270:28:0:0 1 v8
v v10 Copy t2 0 - p2:270:28:2:0 1 v9
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v10,v1
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
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Copy t11 0 - p2:270:36:2:0 1 v6
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v8
v v10 Copy t2 0 - p2:270:28:2:0 1 v9
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:270:270
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:266:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Copy t11 0 - p2:270:36:2:0 0 v6
v v9 Bswap64 t11 0 - p2:270:28:1:0 2 v6
v v10 Copy t2 0 - p2:270:28:2:0 0 v9
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:270:270
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:270:270
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:270:270
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:270:270
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:270:270
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:270:270
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:270:270
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v8,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:270:270
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:266:6:2:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 20 "expand calls"
aux a5 nameoff "x+0" a3 0
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v8 SP t15 0 - p0:0:0:0:0 2 -
v v7 OffPtr t33 0 - p0:0:0:0:0 0 v8
v v5 LocalAddr t33 0 a4 p2:270:2:0:0 0 v8,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 21 "decompose builtin"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v8 SP t15 0 - p0:0:0:0:0 2 -
v v7 OffPtr t33 0 - p0:0:0:0:0 0 v8
v v5 LocalAddr t33 0 a4 p2:270:2:0:0 0 v8,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v8 SP t15 0 - p0:0:0:0:0 2 -
v v7 OffPtr t33 0 - p0:0:0:0:0 0 v8
v v5 LocalAddr t33 0 a4 p2:270:2:0:0 0 v8,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v8 SP t15 0 - p0:0:0:0:0 2 -
v v7 OffPtr t33 0 - p0:0:0:0:0 0 v8
v v5 LocalAddr t33 0 a4 p2:270:2:0:0 0 v8,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 Bswap64 t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 33 "lower"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 36 "pair"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a1 call "AuxCall{math/bits.ReverseBytes}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
fstate scheduled,laidout
regalloc 12 v6:R0,v9:R0,v11:[]
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
fstate scheduled,laidout
regalloc 12 v6:R0,v9:R0,v11:[]
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 11 1
b b1 Ret p2:270:28:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a5 p2:270:28:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v9 ARM64REV t11 0 - p2:270:28:1:0 1 v6
v v11 MakeResult t34 0 - p2:270:2:0:0 1 v9,v1
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
cache linestarts 2:270:270
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

/-- `std/std/math/bits/ReverseBytes,1.prog` (quick-v10). -/
def fProgR : String := r#"gofv-prog 3
pkg "math/bits"
func "ReverseBytes" 1
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
sym y1 "math/bits.ReverseBytes" 1
curfn p2:266:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 266 200080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "math/bits.ReverseBytes.arginfo1" 0
sym y4 "math/bits.ReverseBytes.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:266:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:266:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:266:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:266:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:266:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:266:6:2:0
p 6 6 0 0 0 - REV 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:270:28:1:0
p 7 7 0 0 0 - RET 0 _ 0 - _ 0 0 p2:270:28:2:0
p 8 8 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 266 200080
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p2:266:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:266:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:266:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:266:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:266:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:266:6:2:0
p 6 0 0 0 91 - REV 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:270:28:1:0
p 7 4 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:270:28:2:0
fn y1 8 0 0 0 266 2000c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 16 0 000cc0dac0035fd60000000000000000 0
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
data y11 SRODATA 4 1 28000 9e040400 0
data y12 SRODATA 3 1 28000 000400 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.uint" 0
sym y18 "type:uint" 0
dwfn y13 y14 y15 - y16 "math/bits.ReverseBytes" 1:266 1 0 1 50
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "uint" 0 0 1 p2:266:19:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "uint64" 0 0 1 p2:270:28:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uint" 0 0 1 p2:266:27:0:0
var 0 0 "x" 5 1 0 0 0 8 y17 "math/bits/bits.go" 266 19 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y17 "math/bits/bits.go" 266 27 0 1 0 0 -
scope 0 0 - 0,1
data y13 SDWARFFCN 63 0 0 036d6174682f626974732e526576657273654279746573000010019c020000008a02012d7800008a0200000000000000002e7e723000018a02000000000000 5
reloc 0 0 R_USETYPE 0 y18
reloc 24 1 R_DWTXTADDR_U1 0 y1
reloc 41 4 R_DWARFSECREF 0 y17
reloc 45 4 R_DWARFSECREF 0 y14
reloc 57 4 R_DWARFSECREF 0 y17
data y14 SDWARFLOC 8 0 0 0100040004015000 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y16 SDWARFLINES 24 0 0 00090200000000000000000402038802140637020c000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stInR : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsaR fProgR

def lcR : LocCtx :=
  match stInR with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

def psR : Array GoFV.Asm.Prog :=
  match stInR with
  | .ok x => x.2.1
  | .error _ => #[]

def bsR : ID → Option Nat :=
  match stInR with
  | .ok x => x.2.2.1
  | .error _ => fun _ => none

def gR : G2In :=
  match stInR with
  | .ok x => x.2.2.2
  | .error _ => { syms := #[], slotOp := fun _ => none, stksize := 0 }

/-- The PC table `checkG33` gives (`b1`: one entry per value `v6`, `v1`, `v9`, `v11`, then the `RET`). -/
def tabR : PcTab := [(1, [5, 5, 5, 7, 7])]

/-- The class table `checkG33` gives. -/
def ktR : KTab := (match checkG33 lcR psR bsR gR with
  | .ok (_, k) => k
  | .error _ => [])

def blkR : Block := (lcR.ctx.f.block? 1).getD default

def valR (n : ID) : Value := (lcR.ctx.f.value? n).getD default

def LR : Link := Lof psR

def ER : MatchEnv := Eof lcR psR tabR

/-- The argument `x`. -/
def xR : BitVec 64 := 0x0102030405060708

/-- The `runLoc` state before `v9`: `x = xR` in `R0`, every other register `poison`. -/
def s0R : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w64 xR else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v9`: `X0 = xR`, the activation's `g` and `FP`, the PC of `v9`, a
zero memory. -/
def m0R : MState :=
  { x := fun k => if k = 0 then xR else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := ER.pcOf 1 2, mem := fun _ => 0 }

/-- The register holds the 64-bit integer `0x0807060504030201`. -/
def isResR : Option Val → Bool
  | some (.int .w64 x) => x == 0x0807060504030201
  | _ => false

theorem isResR_spec {o : Option Val} (h : isResR o = true) : o = some (.int .w64 0x0807060504030201) := by
  unfold isResR at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on `ReverseBytes`: it holds an arm64 op, `checkG33` accepts it
with `tabR` and `ktR` and `checkG31` does not; it accesses no frame variable and has no home slot;
`b1` holds `v9` (`REV`) at index 2; `R0` has class 64 before it, where G31's table is
`[]`; `stepLoc` runs `v9` from `s0R` to `R0 = 0x0807060504030201`. -/
def gFactsR : Bool :=
  lcR.ctx.f.lowered &&
    (checkG33 lcR psR bsR gR).toOption == some (tabR, ktR) &&
    (checkG31 lcR psR bsR gR).toOption.isNone &&
    (accessedVars lcR).isEmpty && (homeSlots lcR).isEmpty &&
    lcR.ctx.f.blocks.toList.contains 1 && (lcR.ctx.f.block? 1).isSome &&
    (lcR.ctx.f.value? 9).isSome && blkR.values[2]? == some 9 &&
    (valR 9).op == .ARM64REV &&
    (kAt lcR ktR 1 blkR 2).get 0 == some 64 &&
    uL31 lcR (uIn lcR 1) blkR 2 == [] &&
    GenG1.okThen (stepLoc GenG2.env lcR s0R (valR 9)) fun s1 => isResR s1.regs[0]?

/-! ## `internal/bytealg.Cutover` -/

/-- `std/std/internal/bytealg/Cutover,1.ssa` (quick-v10). -/
def fSsaS : String := r#"gofv-ssa 5.1
pkg "internal/bytealg"
func "Cutover" 1 0 0
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
config localpkg "internal/bytealg"
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
type t2 INT 8 8 0 comparable,named "int" "int"
type t1 FUNC 8 8 8 hasptr,direct "func(int) int" "func(int) int" 0 1 1
field 0 "n" t2 ? 0
field 1 "" t2 ? 0
aux a2 sym "internal/bytealg.Cutover" "internal/bytealg.Cutover" 1 - 0 - - - - 0
posbase p7 "internal/bytealg/index_arm64.go" 1 1 -1
aux a3 name "n" "n" PPARAM t2 0 1 used p7:20:14:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t2 0 1 - p7:20:21:0:0
aux a1 call "AuxCall{internal/bytealg.Cutover}" a2 1 1 1 8 8 1 1
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
type t33 RESULTS ? ? ? - "int,mem" "" 2 t2,t28
slot s1 a3 t2 0 - 0
f b1 t1 a1 12 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t2,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t20 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 0 - p7:22:14:0:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,4=v8,v9
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t20 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 0 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,4=v8,v9
freev -
freeb -
cache postorder b1
cache linestarts 7:22:22
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t20 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 0 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,4=v8,v9
freev -
freeb -
cache postorder b1
cache linestarts 7:22:22
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 0 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 7:22:22
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 0 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 7:22:22
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 0 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 7:22:22
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 0 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 7:22:22
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 7:22:22
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 7:22:22
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 7:22:22
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p7:20:6:2:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "n+0" a3 0
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t20 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t20 0 a4 p7:22:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,4=v8,v9
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t20 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t20 0 a4 p7:22:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,4=v8,v9
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t20 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t20 0 a4 p7:22:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,4=v8,v9
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t20 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t20 0 a4 p7:22:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4,4=v8,v9
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v8 Const64 t2 4 - p0:0:0:0:0 1 -
v v9 Const64 t14 4 - p0:0:0:0:0 1 -
v v10 Rsh64x64 t2 1 - p7:22:14:1:0 1 v6,v9
v v11 Add64 t2 0 - p7:22:11:0:0 1 v8,v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 4=v8,v9
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 7:22:22
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v8,v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{internal/bytealg.Cutover}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v8,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
fstate scheduled,laidout
regalloc 13 v6:R0,v10:R1,v11:R0,v12:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v8,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
fstate scheduled,laidout
regalloc 13 v6:R0,v10:R1,v11:R0,v12:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 12 1
b b1 Ret p7:22:16:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p7:22:16:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64SRAconst t2 4 - p7:22:14:1:0 1 v6
v v11 ARM64ADDconst t2 4 - p7:22:11:0:0 1 v10
v v12 MakeResult t33 0 - p7:22:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v8,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 7:22:22
fstate scheduled,laidout
regalloc 13 v6:R0,v10:R1,v11:R0,v12:[]
dcllen 2
end
frontend
end
ptrcache t2,t5,t6,t7,t8,t10,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t2,t14,t15,t25,t26,t12,t13,t3,t17,t18,t19,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t33
eof
"#

/-- `std/std/internal/bytealg/Cutover,1.prog` (quick-v10). -/
def fProgS : String := r#"gofv-prog 3
pkg "internal/bytealg"
func "Cutover" 1
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
name n1 "n" PPARAM t1 1 "internal/bytealg.n" 0 a3
name n2 "~r0" PPARAMOUT t1 1 "internal/bytealg.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p7 "internal/bytealg/index_arm64.go" 1 1 -1 6 "internal/bytealg/index_arm64.go" "internal/bytealg/index_arm64.go" 1 1
sym y1 "internal/bytealg.Cutover" 1
curfn p7:20:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 20 200080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "internal/bytealg.Cutover.arginfo1" 0
sym y4 "internal/bytealg.Cutover.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p7:20:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p7:20:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p7:20:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p7:20:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p7:20:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p7:20:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p7:22:14:1:0
p 7 7 0 0 0 - ASR 0 CONST/0/0/0/NONE/0/4/-/- 8192 - REG/8193/0/0/NONE/0/0/-/- 0 0 p7:22:14:1:0
p 8 8 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/4/-/- 8193 - REG/8192/0/0/NONE/0/0/-/- 0 0 p7:22:11:2:0
p 9 9 0 0 0 - RET 0 _ 0 - _ 0 0 p7:22:16:2:0
p 10 10 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 20 200080
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
dbgloc 0 1:-10000:1:11:50
dbgregout n2
dbgpc 1:11:9
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p7:20:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p7:20:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p7:20:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p7:20:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p7:20:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p7:20:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p7:22:14:1:0
p 7 0 0 0 274 - ASR 0 CONST/0/0/0/NONE/17/4/-/- 8192 - REG/8193/0/0/NONE/2/0/-/- 0 0 p7:22:14:1:0
p 8 4 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/4/-/- 8193 - REG/8192/0/0/NONE/2/0/-/- 0 0 p7:22:11:2:0
p 9 8 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p7:22:16:2:0
fn y1 8 0 0 0 20 2000c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 16 0 01fc449320100091c0035fd600000000 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 6
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 3 1 28000 010400 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040400 0
data y9 SRODATA 3 1 28000 020400 0
data y10 SRODATA 3 1 28000 0e0400 0
data y11 SRODATA 3 1 28000 2e0400 0
data y12 SRODATA 3 1 28000 000400 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.int" 0
sym y18 "type:int" 0
dwfn y13 y14 y15 - y16 "internal/bytealg.Cutover" 6:20 1 0 1 21
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "int" 0 0 1 p7:20:14:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "int" 0 0 1 p7:20:21:0:0
var 0 0 "n" 5 1 0 0 0 8 y17 "internal/bytealg/index_arm64.go" 20 14 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y17 "internal/bytealg/index_arm64.go" 20 21 0 1 0 0 -
scope 0 0 - 0,1
data y13 SDWARFFCN 62 0 0 03696e7465726e616c2f62797465616c672e4375746f766572000010019c0700000014012d6e00001400000000000000002e7e7230000114000000000000 5
reloc 0 0 R_USETYPE 0 y18
reloc 26 1 R_DWTXTADDR_U1 0 y1
reloc 41 4 R_DWARFSECREF 0 y17
reloc 45 4 R_DWARFSECREF 0 y14
reloc 56 4 R_DWARFSECREF 0 y17
data y14 SDWARFLOC 8 0 0 0100040008015000 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y16 SDWARFLINES 23 0 0 000902000000000000000004070310140637020c000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stInS : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsaS fProgS

def lcS : LocCtx :=
  match stInS with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

def psS : Array GoFV.Asm.Prog :=
  match stInS with
  | .ok x => x.2.1
  | .error _ => #[]

def bsS : ID → Option Nat :=
  match stInS with
  | .ok x => x.2.2.1
  | .error _ => fun _ => none

def gS : G2In :=
  match stInS with
  | .ok x => x.2.2.2
  | .error _ => { syms := #[], slotOp := fun _ => none, stksize := 0 }

/-- The PC table `checkG33` gives (`b1`: one entry per value `v6`, `v1`, `v10`, `v11`, `v12`, then the `RET`). -/
def tabS : PcTab := [(1, [5, 5, 5, 8, 9, 9])]

/-- The class table `checkG33` gives. -/
def ktS : KTab := (match checkG33 lcS psS bsS gS with
  | .ok (_, k) => k
  | .error _ => [])

def blkS : Block := (lcS.ctx.f.block? 1).getD default

def valS (n : ID) : Value := (lcS.ctx.f.value? n).getD default

def LS : Link := Lof psS

def ES : MatchEnv := Eof lcS psS tabS

/-- The argument `n = -256`. -/
def xS : BitVec 64 := 0xffffffffffffff00

/-- The `runLoc` state before `v10`: `n = xS` in `R0`, every other register `poison`. -/
def s0S : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w64 xS else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v10`: `X0 = xS`, the activation's `g` and `FP`, the PC of `v10`, a
zero memory. -/
def m0S : MState :=
  { x := fun k => if k = 0 then xS else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := ES.pcOf 1 2, mem := fun _ => 0 }

/-- The register holds the 64-bit integer `0xfffffffffffffff0`. -/
def isResS : Option Val → Bool
  | some (.int .w64 x) => x == 0xfffffffffffffff0
  | _ => false

theorem isResS_spec {o : Option Val} (h : isResS o = true) : o = some (.int .w64 0xfffffffffffffff0) := by
  unfold isResS at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on `Cutover`: it holds an arm64 op, `checkG33` accepts it
with `tabS` and `ktS` and `checkG31` does not; it accesses no frame variable and has no home slot;
`b1` holds `v10` (`SRAconst`) at index 2; `R0` has class 64 before it, where G31's table is
`[]`; `stepLoc` runs `v10` from `s0S` to `R1 = 0xfffffffffffffff0`. -/
def gFactsS : Bool :=
  lcS.ctx.f.lowered &&
    (checkG33 lcS psS bsS gS).toOption == some (tabS, ktS) &&
    (checkG31 lcS psS bsS gS).toOption.isNone &&
    (accessedVars lcS).isEmpty && (homeSlots lcS).isEmpty &&
    lcS.ctx.f.blocks.toList.contains 1 && (lcS.ctx.f.block? 1).isSome &&
    (lcS.ctx.f.value? 10).isSome && blkS.values[2]? == some 10 &&
    (valS 10).op == .ARM64SRAconst &&
    (kAt lcS ktS 1 blkS 2).get 0 == some 64 &&
    uL31 lcS (uIn lcS 1) blkS 2 == [] &&
    GenG1.okThen (stepLoc GenG2.env lcS s0S (valS 10)) fun s1 => isResS s1.regs[1]?

/-! ## The facts -/

/-- What compiled evaluation checks: `gFactsR` and `gFactsS`. -/
def gFacts : Bool := gFactsR && gFactsS

theorem g33_facts : gFacts = true := by
  native_decide

theorem gFactsR_true : gFactsR = true := by
  have h := g33_facts
  simp only [gFacts, Bool.and_eq_true] at h
  exact h.1

theorem gFactsS_true : gFactsS = true := by
  have h := g33_facts
  simp only [gFacts, Bool.and_eq_true] at h
  exact h.2

/-! ## `REV` -/

/-- The facts of `gFactsR` as hypotheses. -/
theorem factsR :
    lcR.ctx.f.lowered = true ∧ checkG33 lcR psR bsR gR = .ok (tabR, ktR) ∧
      (checkG31 lcR psR bsR gR).toOption = none ∧
      (accessedVars lcR).isEmpty = true ∧ (homeSlots lcR).isEmpty = true ∧
      1 ∈ lcR.ctx.f.blocks.toList ∧ lcR.ctx.f.block? 1 = some blkR ∧
      lcR.ctx.f.value? 9 = some (valR 9) ∧ blkR.values[2]? = some 9 ∧
      (valR 9).op = .ARM64REV ∧ (kAt lcR ktR 1 blkR 2).get 0 = some 64 ∧
      uL31 lcR (uIn lcR 1) blkR 2 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lcR s0R (valR 9)) (fun s1 => isResR s1.regs[0]?) = true := by
  have hf := gFactsR_true
  simp only [gFactsR, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h31, hav, hsl, hmb, hbs, hvs, hi, hop, hk, hu, hrun⟩ := hf
  refine ⟨hl, ?_, h31, hav, hsl, hmb, ?_, ?_, hi, hop, hk, hu, hrun⟩
  · revert hres; cases checkG33 lcR psR bsR gR <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blkR, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [valR, hv]

theorem s0R_regs {r : Nat} {x : Val} (h : s0R.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w64 xR) ∨ x = .poison := by
  simp only [s0R, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0R : LocMatch ER s0R 1 2 m0R where
  regs := by
    intro r v hv
    rcases s0R_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl rfl
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0R] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0R, ER, Eof]; decide,
    by simp only [MState.word, readMem, m0R, ER, Eof]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g33Inv0R (hk : (kAt lcR ktR 1 blkR 2).get 0 = some 64) :
    G3Inv ER lcR (kAt lcR ktR 1 blkR 2) s0R where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0R_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [hk] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0R] at h

/-- The per-value premises of `v9`: none apply. -/
theorem preR {s : LocState} (hop : (valR 9).op = .ARM64REV) : G14Pre lcR s (valR 9) := by
  have hne : ∀ o : Op, o ≠ .ARM64REV → (valR 9).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G33's `REV` on `math/bits.ReverseBytes`**: from the state before `v9` with `x = 0x0102030405060708`
in `R0` (`X0 = x`), `g33_value` runs `REV R0, R0` (`v9`): `runLoc`'s `R0` holds `0x0807060504030201`
and the machine state, related to it before `v11` under an activation extending `ER` that is again
a `G28Env`, has `X0 = 0x0807060504030201`. -/
theorem genG33_un_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lcR s0R (valR 9) = .ok s1 ∧
      s1.regs[0]? = some (.int .w64 0x0807060504030201) ∧
      ER.Extends E1 ∧ G28Env lcR gR LR psR 0 tabR E1 ∧
      PStar GenG2.H0 LR psR.toList 0 m0R m1 ∧
      LocMatch E1 s1 1 3 m1 ∧ m1.x 0 = 0x0807060504030201 := by
  obtain ⟨hl, hc, -, hav, hsl, hmb, hb, hv, hi, hop, hk, hu, hrun⟩ := factsR
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hE : G28Env lcR gR LR psR 0 tabR ER := envOf hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64REV → (valR 9).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g33_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hmb hb hi hv (by rw [hop]; rfl) locMatch0R (g33Inv0R hk)
    (by rw [hu]; intro e he; cases he) (preR hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  have hr1' := isResR_spec hr1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  exact ⟨s1, E1, m1, hs1, hr1', hx1, hE1, hp1, hm1',
    valRel_i64 hA ((hm1'.regs 0 _ hr1').1 0 rfl)⟩

/-! ## `SRAconst` -/

/-- The facts of `gFactsS` as hypotheses. -/
theorem factsS :
    lcS.ctx.f.lowered = true ∧ checkG33 lcS psS bsS gS = .ok (tabS, ktS) ∧
      (checkG31 lcS psS bsS gS).toOption = none ∧
      (accessedVars lcS).isEmpty = true ∧ (homeSlots lcS).isEmpty = true ∧
      1 ∈ lcS.ctx.f.blocks.toList ∧ lcS.ctx.f.block? 1 = some blkS ∧
      lcS.ctx.f.value? 10 = some (valS 10) ∧ blkS.values[2]? = some 10 ∧
      (valS 10).op = .ARM64SRAconst ∧ (kAt lcS ktS 1 blkS 2).get 0 = some 64 ∧
      uL31 lcS (uIn lcS 1) blkS 2 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lcS s0S (valS 10)) (fun s1 => isResS s1.regs[1]?) = true := by
  have hf := gFactsS_true
  simp only [gFactsS, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h31, hav, hsl, hmb, hbs, hvs, hi, hop, hk, hu, hrun⟩ := hf
  refine ⟨hl, ?_, h31, hav, hsl, hmb, ?_, ?_, hi, hop, hk, hu, hrun⟩
  · revert hres; cases checkG33 lcS psS bsS gS <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blkS, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [valS, hv]

theorem s0S_regs {r : Nat} {x : Val} (h : s0S.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w64 xS) ∨ x = .poison := by
  simp only [s0S, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0S : LocMatch ES s0S 1 2 m0S where
  regs := by
    intro r v hv
    rcases s0S_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl rfl
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0S] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0S, ES, Eof]; decide,
    by simp only [MState.word, readMem, m0S, ES, Eof]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g33Inv0S (hk : (kAt lcS ktS 1 blkS 2).get 0 = some 64) :
    G3Inv ES lcS (kAt lcS ktS 1 blkS 2) s0S where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0S_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [hk] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0S] at h

/-- The per-value premises of `v10`: none apply. -/
theorem preS {s : LocState} (hop : (valS 10).op = .ARM64SRAconst) : G14Pre lcS s (valS 10) := by
  have hne : ∀ o : Op, o ≠ .ARM64SRAconst → (valS 10).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G33's `SRAconst` on `internal/bytealg.Cutover`**: from the state before `v10` with `n = -256`
(`xS`) in `R0` (`X0 = xS`), `g33_value` runs `ASR $4, R0, R1` (`v10`, `n >> 4`): `runLoc`'s `R1` holds
`-16` and the machine state, related to it before `v11` under an activation extending `ES` that is
again a `G28Env`, has `X1 = 0xfffffffffffffff0`. -/
theorem genG33_sra_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lcS s0S (valS 10) = .ok s1 ∧
      s1.regs[1]? = some (.int .w64 0xfffffffffffffff0) ∧
      ES.Extends E1 ∧ G28Env lcS gS LS psS 0 tabS E1 ∧
      PStar GenG2.H0 LS psS.toList 0 m0S m1 ∧
      LocMatch E1 s1 1 3 m1 ∧ m1.x 1 = 0xfffffffffffffff0 := by
  obtain ⟨hl, hc, -, hav, hsl, hmb, hb, hv, hi, hop, hk, hu, hrun⟩ := factsS
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hE : G28Env lcS gS LS psS 0 tabS ES := envOf hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64SRAconst → (valS 10).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g33_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hmb hb hi hv (by rw [hop]; rfl) locMatch0S (g33Inv0S hk)
    (by rw [hu]; intro e he; cases he) (preS hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  have hr1' := isResS_spec hr1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  exact ⟨s1, E1, m1, hs1, hr1', hx1, hE1, hp1, hm1',
    valRel_i64 hA ((hm1'.regs 1 _ hr1').1 1 rfl)⟩

end GoFV.Proof.Witness.GenG33
