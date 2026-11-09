import GoFV.Proof.Gen.G33
import GoFV.Proof.Witness.GenG13

/-!
# Non-vacuity witness: slice G33 of the genssa validator on `runtime.(*mspan).pinnerBitSize` and
`runtime.(*_func).isInlined`

Two functions of the corpus `gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim:

* `std/std/runtime/(*mspan).pinnerBitSize,1.ssa` and `…,1.prog` (`fSsaU`, `fProgU`; file names
  `%28%2Amspan%29.pinnerBitSize,1.*`; `runtime/pinner.go`,
  `return divRoundUp(uintptr(s.nelems)*2, 8)`). Block `b2`: `v6 = ArgIntReg` (`s`, `R0`),
  `InitMem`, `v10 = MOVHUload [50] v6` (`s.nelems`, `MOVHU 50(R0), R1`),
  `v13 = UBFIZ [272] v10` (`UBFIZ $1, R1, $16, R1`: the low 16 bits shifted up by 1), `ADDconst`,
  `SRLconst`, `InlMark`, `MakeResult`.
* `std/std/runtime/(*_func).isInlined,1.ssa` and `…,1.prog` (`fSsaC`, `fProgC`; file names
  `%28%2A_func%29.isInlined,1.*`; `runtime/symtab.go`, `return f.entryOff == ^uint32(0)`).
  Block `b1`: `v6 = ArgIntReg` (`f`, `R0`), `InitMem`, `v10 = MOVWUload v6` (`MOVWU (R0), R1`),
  `v3 = CMNWconst [1] v10` (`CMNW $1, R1`), `v12 = Equal v3` (`CSET EQ, R0`), `MakeResult`.

`checkG31` rejects both (`UBFIZ`, `CMNWconst` are G33's ops); `checkG33` accepts them with the PC
tables `tabU`, `tabC` and the class tables `ktU`, `ktC`. Before `v13` and `v3`, G31's upper-bit table
holds the narrow load's register `R1`, zero-extended from 16 and 32 bits.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g33b_facts`),
`stepLoc` runs `v13` from a state with the 16-bit `s.nelems = 0xbeef` in `R1`: `R1` then holds the
64-bit `0x17dde`; and `v3` from a state with the 32-bit `f.entryOff = 0xffffffff` in `R1`: the
flags then have `Z` set. On a framed activation with `G28Env`, `g33_value` runs the
`UBFIZ $1, R1, $16, R1` (`genG33_ubfiz_witness`: the machine's `X1` is `0x17dde`) and the
`CMNW $1, R1` (`genG33_cmnw_witness`: the machine's `Z` flag is set).
-/

namespace GoFV.Proof.Witness.GenG33b

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

/-! ## `runtime.(*mspan).pinnerBitSize` -/

/-- `std/std/runtime/(*mspan).pinnerBitSize,1.ssa` (quick-v10). -/
def fSsaU : String := r#"gofv-ssa 5.1
pkg "runtime"
func "(*mspan).pinnerBitSize" 1 0 0
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
type t5 STRUCT 0 1 0 notinheap,comparable,named "sys.nih" "internal/runtime/sys.nih" 0
type t4 STRUCT 0 1 0 notinheap,comparable,named "sys.NotInHeap" "internal/runtime/sys.NotInHeap" 1
field 0 "_" t5 0 0
type t7 STRUCT 16 8 0 notinheap,comparable,named "mSpanList" "runtime.mSpanList" 3
field 0 "_" t4 0 0
field 1 "first" t2 0 0
field 2 "last" t2 8 0
type t6 PTR 8 8 0 comparable "*mSpanList" "*runtime.mSpanList" t7
type t8 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t9 UINTPTR 8 8 0 comparable,named "gclinkptr" "runtime.gclinkptr"
type t10 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t11 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t14 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t13 STRUCT 1 1 0 notinheap,comparable,named "gcBits" "runtime.gcBits" 2
field 0 "_" t4 0 0
field 1 "x" t14 0 0
type t12 PTR 8 8 0 comparable "*gcBits" "*runtime.gcBits" t13
type t15 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t16 UINT8 1 1 0 comparable,named "spanClass" "runtime.spanClass"
type t19 STRUCT 0 1 0 comparable,named "atomic.noCopy" "internal/runtime/atomic.noCopy" 0
type t18 STRUCT 1 1 0 comparable,named "atomic.Uint8" "internal/runtime/atomic.Uint8" 2
field 0 "noCopy" t19 0 0
field 1 "value" t14 0 0
type t17 STRUCT 1 1 0 comparable,named "mSpanStateBox" "runtime.mSpanStateBox" 1
field 0 "s" t18 0 0
type t20 BOOL 1 1 0 comparable,named "bool" "bool"
type t22 STRUCT 0 1 0 comparable,named "lockRankStruct" "runtime.lockRankStruct" 0
type t21 STRUCT 8 8 0 comparable,named "mutex" "runtime.mutex" 2
field 0 "lockRankStruct" t22 0 1
field 1 "key" t8 0 0
type t25 UINT8 1 1 0 comparable,named "byte" "uint8"
type t24 STRUCT 24 8 0 notinheap,comparable,named "special" "runtime.special" 4
field 0 "_" t4 0 0
field 1 "next" t23 0 0
field 2 "offset" t8 8 0
field 3 "kind" t25 16 0
type t23 PTR 8 8 0 comparable "*special" "*runtime.special" t24
type t27 STRUCT 8 8 0 comparable,named "offAddr" "runtime.offAddr" 1
field 0 "a" t8 0 0
type t26 STRUCT 16 8 0 comparable,named "addrRange" "runtime.addrRange" 2
field 0 "base" t27 0 0
field 1 "limit" t27 8 0
type t30 UINT8 1 1 0 comparable,named "abi.TFlag" "internal/abi.TFlag"
type t31 UINT8 1 1 0 comparable,named "abi.Kind" "internal/abi.Kind"
type t33 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t32 FUNC 8 8 8 hasptr,direct "func(unsafe.Pointer, unsafe.Pointer) bool" "func(unsafe.Pointer, unsafe.Pointer) bool" 0 2 1
field 0 "" t33 ? 0
field 1 "" t33 ? 0
field 2 "" t20 ? 0
type t34 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t25
type t35 INT32 4 4 0 comparable,named "abi.NameOff" "internal/abi.NameOff"
type t36 INT32 4 4 0 comparable,named "abi.TypeOff" "internal/abi.TypeOff"
type t29 STRUCT 48 8 40 hasptr,named "abi.Type" "internal/abi.Type" 11
field 0 "Size_" t8 0 0
field 1 "PtrBytes" t8 8 0
field 2 "Hash" t15 16 0
field 3 "TFlag" t30 20 0
field 4 "Align_" t14 21 0
field 5 "FieldAlign_" t14 22 0
field 6 "Kind_" t31 23 0
field 7 "Equal" t32 24 0
field 8 "GCData" t34 32 0
field 9 "Str" t35 40 0
field 10 "PtrToThis" t36 44 0
type t28 PTR 8 8 8 hasptr,direct,comparable "*abi.Type" "*internal/abi.Type" t29
type t3 STRUCT 160 8 160 hasptr,notinheap,comparable,named "mspan" "runtime.mspan" 28
field 0 "_" t4 0 0
field 1 "next" t2 0 0
field 2 "prev" t2 8 0
field 3 "list" t6 16 0
field 4 "startAddr" t8 24 0
field 5 "npages" t8 32 0
field 6 "manualFreeList" t9 40 0
field 7 "freeindex" t10 48 0
field 8 "nelems" t10 50 0
field 9 "freeIndexForScan" t10 52 0
field 10 "allocCache" t11 56 0
field 11 "allocBits" t12 64 0
field 12 "gcmarkBits" t12 72 0
field 13 "pinnerBits" t12 80 0
field 14 "sweepgen" t15 88 0
field 15 "divMul" t15 92 0
field 16 "allocCount" t10 96 0
field 17 "spanclass" t16 98 0
field 18 "state" t17 99 0
field 19 "needzero" t14 100 0
field 20 "isUserArenaChunk" t20 101 0
field 21 "allocCountBeforeCache" t10 102 0
field 22 "elemsize" t8 104 0
field 23 "limit" t8 112 0
field 24 "speciallock" t21 120 0
field 25 "specials" t23 128 0
field 26 "userArenaChunkFree" t26 136 0
field 27 "largeType" t28 152 0
type t2 PTR 8 8 0 comparable "*mspan" "*runtime.mspan" t3
type t1 FUNC 8 8 8 hasptr,direct "method(*mspan) func() uintptr" "method(*runtime.mspan) func() uintptr" 1 0 1
field 0 "s" t2 ? 0
field 1 "" t8 ? 0
aux a2 sym "runtime.(*mspan).pinnerBitSize" "runtime.(*mspan).pinnerBitSize" 1 - 0 - - - - 0
posbase p52 "runtime/pinner.go" 1 1 -1
aux a3 name "s" "s" PPARAM t2 0 1 used p52:290:7:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t8 0 1 - p52:290:33:0:0
aux a1 call "AuxCall{runtime.(*mspan).pinnerBitSize}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t8 a4 0 -1
type t37 INT8 1 1 0 comparable,named "int8" "int8"
type t38 INT16 2 2 0 comparable,named "int16" "int16"
type t39 INT32 4 4 0 comparable,named "int32" "int32"
type t40 INT64 8 8 0 comparable,named "int64" "int64"
type t41 INT 8 8 0 comparable,named "int" "int"
type t42 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t43 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t44 UINT 8 8 0 comparable,named "uint" "uint"
type t45 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t46 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t14
type t47 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t39
type t48 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t15
type t49 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t41
type t50 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t8
type t51 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t42
type t52 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t43
type t53 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t46
type t54 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t55 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t56 SSA ? ? ? - "mem" ""
type t57 SSA ? ? ? - "flags" ""
type t58 SSA ? ? ? - "void" ""
type t59 SSA 16 8 ? - "int128" ""
type t60 RESULTS ? ? ? - "mem" "" 1 t56
type t61 PTR 8 8 8 hasptr,direct,comparable "**mspan" "**runtime.mspan" t2
type t62 PTR 8 8 8 hasptr,direct,comparable "*uint16" "*uint16" t10
posbase p391 "runtime/stubs.go" 1 1 118
type t63 RESULTS ? ? ? - "uintptr,mem" "" 2 t8,t56
slot s1 a3 t2 0 - 0
aux a5 name "n" "n" PAUTO t8 0 1 used p391:397:17:0:0
slot s2 a5 t8 0 - 0
aux a6 name "a" "a" PAUTO t8 0 1 used p391:397:20:0:0
slot s3 a6 t8 0 - 0
aux a7 name "~r0" "~r0" PAUTO t8 0 1 - p391:397:31:0:0
slot s4 a7 t8 0 - 0
f b1 t1 a1 22 2
typs Bool=t20,Int8=t37,Int16=t38,Int32=t39,Int64=t40,UInt8=t14,UInt16=t10,UInt32=t15,UInt64=t11,Int=t41,Float32=t42,Float64=t43,UInt=t44,Uintptr=t8,String=t45,BytePtr=t46,Int32Ptr=t47,UInt32Ptr=t48,IntPtr=t49,UintptrPtr=t50,Float32Ptr=t51,Float64Ptr=t52,BytePtrPtr=t53,Complex64=t54,Complex128=t55,UnsafePtr=t33,Mem=t56,Flags=t57,Void=t58,Int128=t59,ResultMem=t60
b b1 Plain p52:291:19:1:0 0 0 - - b2:0 -
v v1 InitMem t56 0 - p0:0:0:0:0 6 -
v v2 SP t8 0 - p0:0:0:0:0 2 -
v v3 SB t8 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t61 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t50 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v7 Const64 t8 0 - p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p52:291:29:0:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v14 Const64 t8 8 - p0:0:0:0:0 2 -
v v15 InlMark t58 118 - p52:291:19:1:0 0 v1
v v16 Add64 t8 0 - p391:400:12:0:0 1 v13,v14
v v17 Const64 t8 1 - p0:0:0:0:0 1 -
v v18 Sub64 t8 0 - p391:400:16:0:0 1 v16,v17
v v19 Div64u t8 0 - p391:400:21:0:0 1 v18,v14
b b2 Ret p52:291:2:1:0 0 0 - v22 - b1:0
v v20 Copy t8 0 - p52:291:2:2:0 1 v19
v v21 Copy t56 0 - p52:291:2:2:0 1 v1
v v22 MakeResult t63 0 - p52:291:2:0:0 1 v20,v21
names s1,s2,s3,s4
named s1 v6
named s2 v13
named s3 v14
named s4 v19,v20
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v7,1=v17,2=v12,8=v14
freev -
freeb -
dcllen 5
end
pass 1 "number lines"
f b1 t1 a1 22 2
b b1 Plain p52:291:19:1:0 0 0 - - b2:0 -
v v1 InitMem t56 0 - p0:0:0:0:0 6 -
v v2 SP t8 0 - p0:0:0:0:0 2 -
v v3 SB t8 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t61 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t50 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v7 Const64 t8 0 - p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v14 Const64 t8 8 - p0:0:0:0:0 2 -
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v16 Add64 t8 0 - p391:400:12:1:0 1 v13,v14
v v17 Const64 t8 1 - p0:0:0:0:0 1 -
v v18 Sub64 t8 0 - p391:400:16:0:0 1 v16,v17
v v19 Div64u t8 0 - p391:400:21:0:0 1 v18,v14
b b2 Ret p52:291:2:1:0 0 0 - v22 - b1:0
v v20 Copy t8 0 - p52:291:2:2:0 1 v19
v v21 Copy t56 0 - p52:291:2:2:0 1 v1
v v22 MakeResult t63 0 - p52:291:2:0:0 1 v20,v21
names s1,s2,s3,s4
named s1 v6
named s2 v13
named s3 v14
named s4 v19,v20
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v7,1=v17,2=v12,8=v14
freev -
freeb -
cache postorder b2,b1
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 22 2
b b1 Plain p52:291:19:1:0 0 0 - - b2:0 -
v v1 InitMem t56 0 - p0:0:0:0:0 7 -
v v2 SP t8 0 - p0:0:0:0:0 2 -
v v3 SB t8 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t61 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t50 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v7 Const64 t8 0 - p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v14 Const64 t8 8 - p0:0:0:0:0 2 -
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v16 Add64 t8 0 - p391:400:12:1:0 1 v13,v14
v v17 Const64 t8 1 - p0:0:0:0:0 1 -
v v18 Sub64 t8 0 - p391:400:16:0:0 1 v16,v17
v v19 Div64u t8 0 - p391:400:21:0:0 2 v18,v14
b b2 Ret p52:291:2:1:0 0 0 - v22 - b1:0
v v20 Copy t8 0 - p52:291:2:2:0 0 v19
v v21 Copy t56 0 - p52:291:2:2:0 0 v1
v v22 MakeResult t63 0 - p52:291:2:0:0 1 v19,v1
names s1,s2,s3,s4
named s1 v6
named s2 v13
named s3 v14
named s4 v19,v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v7,1=v17,2=v12,8=v14
freev -
freeb -
cache postorder b2,b1
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 3 "early deadcode"
f b1 t1 a1 22 2
b b1 Plain p52:291:19:1:0 0 0 - - b2:0 -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v14 Const64 t8 8 - p0:0:0:0:0 2 -
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v16 Add64 t8 0 - p391:400:12:1:0 1 v13,v14
v v17 Const64 t8 1 - p0:0:0:0:0 1 -
v v18 Sub64 t8 0 - p391:400:16:0:0 1 v16,v17
v v19 Div64u t8 0 - p391:400:21:0:0 1 v18,v14
b b2 Ret p52:291:2:1:0 0 0 - v22 - b1:0
v v22 MakeResult t63 0 - p52:291:2:0:0 1 v19,v1
names s1,s2,s3,s4
named s1 v6
named s2 v13
named s3 v14
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 1=v17,2=v12,8=v14
freev v21,v20,v7,v5,v4,v3,v2
freeb -
cache postorder b2,b1
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 4 "short circuit"
f b2 t1 a1 22 2
b b1 BlockInvalid p52:291:19:1:0 0 0 - - - -
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v14 Const64 t8 8 - p0:0:0:0:0 2 -
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v16 Add64 t8 0 - p391:400:12:1:0 1 v13,v14
v v17 Const64 t8 1 - p0:0:0:0:0 1 -
v v18 Sub64 t8 0 - p391:400:16:0:0 1 v16,v17
v v19 Div64u t8 0 - p391:400:21:0:0 1 v18,v14
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s3,s4
named s1 v6
named s2 v13
named s3 v14
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 1=v17,2=v12,8=v14
freev v21,v20,v7,v5,v4,v3,v2
freeb -
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 5 "decompose user"
f b2 t1 a1 22 2
b b1 BlockInvalid p52:291:19:1:0 0 0 - - - -
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v14 Const64 t8 8 - p0:0:0:0:0 2 -
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v16 Add64 t8 0 - p391:400:12:1:0 1 v13,v14
v v17 Const64 t8 1 - p0:0:0:0:0 1 -
v v18 Sub64 t8 0 - p391:400:16:0:0 1 v16,v17
v v19 Div64u t8 0 - p391:400:21:0:0 1 v18,v14
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s3,s4
named s1 v6
named s2 v13
named s3 v14
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 1=v17,2=v12,8=v14
freev v21,v20,v7,v5,v4,v3,v2
freeb -
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 6 "pre-opt deadcode"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v14 Const64 t8 8 - p0:0:0:0:0 2 -
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v16 Add64 t8 0 - p391:400:12:1:0 1 v13,v14
v v17 Const64 t8 1 - p0:0:0:0:0 1 -
v v18 Sub64 t8 0 - p391:400:16:0:0 1 v16,v17
v v19 Div64u t8 0 - p391:400:21:0:0 1 v18,v14
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s3,s4
named s1 v6
named s2 v13
named s3 v14
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 1=v17,2=v12,8=v14
freev v21,v20,v7,v5,v4,v3,v2
freeb b1
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 7 "opt"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
names s1,s2,s3,s4
named s1 v6
named s2 v13
named s3 v14
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 2=v12
freev v21,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 8 "zero arg cse"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
names s1,s2,s3,s4
named s1 v6
named s2 v13
named s3 v14
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 2=v12
freev v21,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 9 "opt deadcode"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 2=v12
freev v21,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 10 "generic cse"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 2=v12
freev v21,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 11 "phiopt"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 2=v12
freev v21,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 12 "gcse deadcode"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 2=v12
freev v21,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 13 "nilcheckelim"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 2=v12
freev v21,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 14 "prove"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 2=v12
freev v21,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 15 "divisible"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 2=v12
freev v21,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 16 "divmod"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v12 Const64 t8 2 - p0:0:0:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Mul64 t8 0 - p52:291:37:0:0 1 v11,v12
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 2=v12
freev v21,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 17 "middle opt"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 18 "known bits"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 19 "early fuse"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p52:290:6:2:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v12,v17,v16,v14,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 20 "expand calls"
aux a8 nameoff "s+0" a3 0
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
v v12 SB t8 0 - p0:0:0:0:0 0 -
v v17 SP t8 0 - p0:0:0:0:0 2 -
v v16 OffPtr t61 0 - p0:0:0:0:0 0 v17
v v14 LocalAddr t50 0 a4 p52:291:2:1:0 0 v17,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v16
freev v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 21 "decompose builtin"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
v v12 SB t8 0 - p0:0:0:0:0 0 -
v v17 SP t8 0 - p0:0:0:0:0 2 -
v v16 OffPtr t61 0 - p0:0:0:0:0 0 v17
v v14 LocalAddr t50 0 a4 p52:291:2:1:0 0 v17,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v16
freev v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 22 "softfloat"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
v v12 SB t8 0 - p0:0:0:0:0 0 -
v v17 SP t8 0 - p0:0:0:0:0 2 -
v v16 OffPtr t61 0 - p0:0:0:0:0 0 v17
v v14 LocalAddr t50 0 a4 p52:291:2:1:0 0 v17,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v16
freev v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 23 "branchelim"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 5 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
v v12 SB t8 0 - p0:0:0:0:0 0 -
v v17 SP t8 0 - p0:0:0:0:0 2 -
v v16 OffPtr t61 0 - p0:0:0:0:0 0 v17
v v14 LocalAddr t50 0 a4 p52:291:2:1:0 0 v17,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts 0=v16
freev v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 24 "late opt"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 25 "dead auto elim"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 26 "sccp"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 27 "generic deadcode"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 28 "late fuse"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 29 "check bce"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 30 "dse"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 31 "memcombine"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 32 "writebarrier"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v7 Const64 t8 7 - p391:400:16:0:0 1 -
v v20 Const64 t11 3 - p391:400:21:0:0 1 -
v v8 NilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v9 OffPtr t62 50 - p52:291:29:0:0 1 v8
v v10 Load t10 0 - p52:291:29:0:0 1 v9,v1
v v11 ZeroExt16to64 t8 0 - p52:291:29:0:0 1 v10
v v13 Lsh64x64 t8 1 - p52:291:37:0:0 1 v11,v21
v v18 Add64 t8 0 - p391:400:16:1:0 1 v7,v13
v v19 Rsh64Ux64 t8 1 - p391:400:21:0:0 1 v18,v20
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
v v21 Const64 t11 1 - p52:291:37:0:0 1 -
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 33 "lower"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 34 "addressing modes"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 35 "late lower"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 36 "pair"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 37 "lowered deadcode for cse"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 38 "lowered cse"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 39 "elim unread autos"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 40 "tighten tuple selectors"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 41 "lowered deadcode"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 42 "checkLower"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 43 "loop invariant"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 44 "late phielim and copyelim"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 45 "tighten"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 46 "late deadcode"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 47 "critical"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 48 "phi tighten"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 49 "likelyadjust"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
dcllen 5
end
pass 50 "layout"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p52:291:29:1:0 1 v6,v1
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v8,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
fstate laidout
dcllen 5
end
pass 51 "schedule"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 2 -
v v1 InitMem t56 0 - p0:0:0:0:0 4 -
v v8 ARM64LoweredNilCheck t58 0 - p52:291:29:1:0 0 v6,v1
v v10 ARM64MOVHUload t10 50 - p52:291:29:0:0 1 v6,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
fstate scheduled,laidout
dcllen 5
end
pass 52 "late nilcheck"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v1 InitMem t56 0 - p0:0:0:0:0 3 -
v v10 ARM64MOVHUload t10 50 - p52:291:29:1:0 1 v6,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
fstate scheduled,laidout
dcllen 5
end
pass 53 "flagalloc"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v1 InitMem t56 0 - p0:0:0:0:0 3 -
v v10 ARM64MOVHUload t10 50 - p52:291:29:1:0 1 v6,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v21,v11,v9,v20,v7,v14,v16,v17,v12,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
fstate scheduled,laidout
dcllen 5
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.(*mspan).pinnerBitSize}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t8 a4 0 -1
callreg 0:1 - 0 -
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v1 InitMem t56 0 - p0:0:0:0:0 3 -
v v10 ARM64MOVHUload t10 50 - p52:291:29:1:0 1 v6,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v2,v3,v4,v5,v7,v9,v11,v12,v14,v16,v17,v20,v21
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
fstate scheduled,laidout
regalloc 23 v6:R0,v10:R1,v13:R1,v18:R1,v19:R0,v22:[]
dcllen 5
end
pass 55 "loop rotate"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v1 InitMem t56 0 - p0:0:0:0:0 3 -
v v10 ARM64MOVHUload t10 50 - p52:291:29:1:0 1 v6,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v2,v3,v4,v5,v7,v9,v11,v12,v14,v16,v17,v20,v21
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
fstate scheduled,laidout
regalloc 23 v6:R0,v10:R1,v13:R1,v18:R1,v19:R0,v22:[]
dcllen 5
end
pass 56 "trim"
f b2 t1 a1 22 2
b b2 Ret p52:291:2:1:0 0 0 - v22 - -
v v6 ArgIntReg t2 0 a8 p52:291:2:1:0 1 -
v v1 InitMem t56 0 - p0:0:0:0:0 3 -
v v10 ARM64MOVHUload t10 50 - p52:291:29:1:0 1 v6,v1
v v13 ARM64UBFIZ t8 272 - p52:291:37:0:0 1 v10
v v18 ARM64ADDconst t8 7 - p391:400:16:1:0 1 v13
v v19 ARM64SRLconst t8 3 - p391:400:21:0:0 1 v18
v v15 InlMark t58 118 - p52:291:19:0:0 0 v1
v v22 MakeResult t63 0 - p52:291:2:1:0 1 v19,v1
names s1,s2,s4
named s1 v6
named s2 v13
named s4 v19
splits -
canon a3/t2/0/-/0=s1,a5/t8/0/-/0=s2,a6/t8/0/-/0=s3,a7/t8/0/-/0=s4
consts -
freev v2,v3,v4,v5,v7,v9,v11,v12,v14,v16,v17,v20,v21
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 52:291:291,391:400:400
fstate scheduled,laidout
regalloc 23 v6:R0,v10:R1,v13:R1,v18:R1,v19:R0,v22:[]
dcllen 5
end
frontend
end
ptrcache t2,t3,t7,t8,t10,t11,t12,t13,t14,t15,t17,t18,t19,t20,t21,t23,t24,t25,t26,t28,t29,t33,t34,t35,t37,t38,t39,t40,t41,t42,t43,t44,t45,t46,t50,t53,t54,t55
typelink t14=t25,t34=t46,t56=t60
typecmp t14 t25 eq
typeorder t37,t25,t31,t14,t30,t16,t38,t10,t39,t35,t36,t15,t40,t11,t41,t44,t8,t9,t54,t55,t42,t43,t20,t34=t46,t62,t47,t48,t49,t50,t51,t52,t53,t61,t28,t2,t12,t23,t6,t32,t1,t5,t29,t3,t21,t18,t13,t19,t27,t24,t26,t7,t4,t17,t22,t45,t33,t56,t58,t57,t59,t60,t63
eof
"#

/-- `std/std/runtime/(*mspan).pinnerBitSize,1.prog` (quick-v10). -/
def fProgU : String := r#"gofv-prog 3
pkg "runtime"
func "(*mspan).pinnerBitSize" 1
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
type t1 8 8 0 0 - "*mspan"
name n1 "s" PPARAM t1 1 "runtime.s" 0 a3
type t2 8 8 0 0 - "uintptr"
name n2 "~r0" PPARAMOUT t2 1 "runtime.~r0" 0 a4
name n3 "n" PAUTO t2 1 "runtime.n" 0 a5
name n4 "a" PAUTO t2 1 "runtime.a" 0 a6
name n5 "~r0" PAUTO t2 1 "runtime.~r0" 0 a7
in n1 0 used
in n2 0 outregs
in n3 0 used
in n4 0 used
in n5 0 -
out n1 0 used
opt n4 0 -
opt n3 0 -
opt n2 0 outregs
opt n5 0 -
stack 0 0 8
end
genin
posbase p52 "runtime/pinner.go" 1 1 -1 51 "runtime/pinner.go" "runtime/pinner.go" 1 1
sym y1 "runtime.(*mspan).pinnerBitSize" 1
curfn p52:290:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 290 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.(*mspan).pinnerBitSize.arginfo1" 0
sym y4 "runtime.(*mspan).pinnerBitSize.argliveinfo" 0
sym y5 "runtime.divRoundUp" 1
inl i118 - p52:291:19:0:0 y5 "divRoundUp"
posbase p391 "runtime/stubs.go" 1 1 118 84 "runtime/stubs.go" "runtime/stubs.go" 1 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p52:290:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p52:290:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p52:290:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p52:290:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p52:290:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p52:290:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p52:291:29:1:0
p 7 7 0 0 0 - MOVHU 0 MEM/8192/0/0/NONE/0/50/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p52:291:29:1:0
p 8 8 0 0 0 - UBFIZ 0 CONST/0/0/0/NONE/0/1/-/- 8193 0:CONST/0/0/0/NONE/0/16/-/- REG/8193/0/0/NONE/0/0/-/- 0 0 p52:291:37:2:0
p 9 9 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/7/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p391:400:16:1:0
p 10 10 0 0 0 - LSR 0 CONST/0/0/0/NONE/0/3/-/- 8193 - REG/8192/0/0/NONE/0/0/-/- 0 0 p391:400:21:2:0
p 11 11 0 0 0 - NOP 0 _ 0 - _ 0 0 p0:0:0:0:0
p 12 12 0 0 0 - RET 0 _ 0 - _ 0 0 p52:291:2:1:0
p 13 13 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 290 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
inlmark @7 118
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 2
dbgslot 0 n1 t1 0
dbgslot 1 n3 t2 0
dbgslot 2 n5 t2 0
dbgvar 0 n1 0
dbgvar 1 n3 1
dbgloc 0 2:-10000:2:19:50
dbgloc 1 2:13:2:18:51
dbgregout n2
dbgpc 2:19:11,2:13:9,2:18:10
end
asm
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p52:290:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p52:290:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p52:290:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p52:290:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p52:290:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p52:290:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p52:291:29:1:0
p 7 0 0 0 361 - MOVHU 0 MEM/8192/0/0/NONE/89/50/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p52:291:29:1:0
p 8 4 0 0 81 - UBFIZ 0 CONST/0/0/0/NONE/17/1/-/- 8193 0:CONST/0/0/0/NONE/17/16/-/- REG/8193/0/0/NONE/2/0/-/- 0 0 p52:291:37:2:0
p 9 8 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/7/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p391:400:16:1:0
p 10 12 0 0 274 - LSR 0 CONST/0/0/0/NONE/17/3/-/- 8193 - REG/8192/0/0/NONE/2/0/-/- 0 0 p391:400:21:2:0
p 11 16 0 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p0:0:0:0:0
p 12 16 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p52:291:2:1:0
fn y1 8 0 0 0 290 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
inlmark @7 118
funcaux y2 y2 - - y3 y4 -
text 32 0 01644079213c7fd3211c009120fc43d3c0035fd6000000000000000000000000 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y2,_,_,_,y3,y4
usedfiles 51,84
inltree 0 -1 p52:291:19:0:0 y5 "divRoundUp" 0
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y6 SRODATA 3 1 28000 010800 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 040800 0
data y10 SRODATA 3 1 28000 020800 0
data y11 SRODATA 7 1 28000 68024202410400 0
data y12 SRODATA 10 1 28000 c80402da0102d9010400 0
data y13 SRODATA 7 1 28000 00020202010400 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.runtime.(*mspan).pinnerBitSize$abstract" 0
sym y18 "" 0
posbase p86 "runtime/stubs.go" 1 1 -1 84 "runtime/stubs.go" "runtime/stubs.go" 1 1
sym y19 "go:info.runtime.divRoundUp$abstract" 0
sym y20 "go:info.*runtime.mspan" 0
sym y21 "go:info.uintptr" 0
sym y22 "type:uintptr" 0
dwfn y14 y15 y16 y17 y18 "runtime.(*mspan).pinnerBitSize" 51:290 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y17 n1,n2
dwinlfn y5 y19
dwinldcl y5 "n" 0 p86:397:17:0:0
dwinldcl y5 "a" 0 p86:397:20:0:0
dwinldcl y5 "~r0" 0 p86:397:31:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime.mspan" 0 0 1 p52:290:7:0:0
dwname n4 1 0 0 1 0 0 0 0 - - "uintptr" 0 0 1 p391:397:20:0:0
dwname n3 1 0 0 1 0 0 0 0 - - "uintptr" 0 0 1 p391:397:17:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uintptr" 0 0 1 p52:290:33:0:0
dwname n5 1 0 0 1 0 0 0 0 - - "uintptr" 0 0 1 p391:397:31:0:0
var 0 0 "s" 5 1 0 0 0 8 y20 "runtime/pinner.go" 290 7 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y21 "runtime/pinner.go" 290 33 0 1 0 0 -
var 2 0 "n" 5 1 0 1 0 -8 y21 "runtime/stubs.go" 397 17 119 0 1 0 v1
scope 0 0 - 0,1,2
inlcall 0 118 51:291 y19 - 1 8:16 2
dieref y14 3 y17 0
dieref y14 8 y19 0
dieoff y17 0:36
data y14 SDWARFFCN 58 0 0 0600000000000020019c2900000000000000002e7e72300001a202000000000009000000000000000034000000a3022900000000000000000000 10
reloc 0 0 R_USETYPE 0 y22
reloc 1 4 R_DWARFSECREF 0 y17
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y17
reloc 15 4 R_DWARFSECREF 0 y15
reloc 27 4 R_DWARFSECREF 0 y21
reloc 33 4 R_DWARFSECREF 0 y19
reloc 37 4 R_DWARFSECREF 0 y16
reloc 48 4 R_DWARFSECREF 0 y19
reloc 52 4 R_DWARFSECREF 9 y15
data y15 SDWARFLOC 18 0 0 01000004001001500001000004080c015100 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
data y16 SDWARFRANGE 7 0 0 01000004081000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y18 SDWARFLINES 40 0 0 00090200000000000000000434039d0214063704550603e8003c063704340603977f330210000101 1
reloc 3 8 R_ADDR 0 y1
data y17 SDWARFABSFCN 45 0 1 0572756e74696d652e282a6d7370616e292e70696e6e657242697453697a650001a20201227300000000000000 1
reloc 40 4 R_DWARFSECREF 0 y20
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stInU : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsaU fProgU

def lcU : LocCtx :=
  match stInU with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

def psU : Array GoFV.Asm.Prog :=
  match stInU with
  | .ok x => x.2.1
  | .error _ => #[]

def bsU : ID → Option Nat :=
  match stInU with
  | .ok x => x.2.2.1
  | .error _ => fun _ => none

def gU : G2In :=
  match stInU with
  | .ok x => x.2.2.2
  | .error _ => { syms := #[], slotOp := fun _ => none, stksize := 0 }

/-- The PC table `checkG33` gives (`b2`: one entry per value `v6`, `v1`, `v10`, `v13`, `v18`, `v19`, `v15`, `v22`, then the `RET`). -/
def tabU : PcTab := [(2, [5, 5, 5, 8, 9, 10, 11, 11, 11])]

/-- The class table `checkG33` gives. -/
def ktU : KTab := (match checkG33 lcU psU bsU gU with
  | .ok (_, k) => k
  | .error _ => [])

def blkU : Block := (lcU.ctx.f.block? 2).getD default

def valU (n : ID) : Value := (lcU.ctx.f.value? n).getD default

def LU : Link := Lof psU

def EU : MatchEnv := Eof lcU psU tabU

/-- The `runLoc` state before `v13`: the 16-bit `s.nelems = 0xbeef` in `R1`, every other register `poison`. -/
def s0U : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 1 then .int .w16 0xbeef else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v13`: `X1 = 0xbeef`, the activation's `g` and `FP`, the PC of `v13`, a
zero memory. -/
def m0U : MState :=
  { x := fun k => if k = 1 then 0xbeef else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := EU.pcOf 2 3, mem := fun _ => 0 }

/-- The register holds the 64-bit integer `0x17dde`. -/
def isResU : Option Val → Bool
  | some (.int .w64 x) => x == 0x17dde
  | _ => false

theorem isResU_spec {o : Option Val} (h : isResU o = true) : o = some (.int .w64 0x17dde) := by
  unfold isResU at h
  split at h
  · rw [beq_iff_eq] at h; rw [h]
  · cases h

/-- What compiled evaluation checks on `pinnerBitSize`: it holds an arm64 op, `checkG33` accepts it
with `tabU` and `ktU` and `checkG31` does not; it accesses no frame variable and has no home slot;
`b2` holds `v13` (`UBFIZ`) at index 3; `R1` has class 16 before it, where G31's table is
`[(1, 16, false)]`; `stepLoc` runs `v13` from `s0U` to `R1 = 0x17dde` (64 bits). -/
def gFactsU : Bool :=
  lcU.ctx.f.lowered &&
    (checkG33 lcU psU bsU gU).toOption == some (tabU, ktU) &&
    (checkG31 lcU psU bsU gU).toOption.isNone &&
    (accessedVars lcU).isEmpty && (homeSlots lcU).isEmpty &&
    lcU.ctx.f.blocks.toList.contains 2 && (lcU.ctx.f.block? 2).isSome &&
    (lcU.ctx.f.value? 13).isSome && blkU.values[3]? == some 13 &&
    (valU 13).op == .ARM64UBFIZ &&
    (kAt lcU ktU 2 blkU 3).get 1 == some 16 &&
    uL31 lcU (uIn lcU 2) blkU 3 == [(1, 16, false)] &&
    GenG1.okThen (stepLoc GenG2.env lcU s0U (valU 13)) fun s1 => isResU s1.regs[1]?

/-! ## `runtime.(*_func).isInlined` -/

/-- `std/std/runtime/(*_func).isInlined,1.ssa` (quick-v10). -/
def fSsaC : String := r#"gofv-ssa 5.1
pkg "runtime"
func "(*_func).isInlined" 1 0 0
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
type t5 STRUCT 0 1 0 notinheap,comparable,named "sys.nih" "internal/runtime/sys.nih" 0
type t4 STRUCT 0 1 0 notinheap,comparable,named "sys.NotInHeap" "internal/runtime/sys.NotInHeap" 1
field 0 "_" t5 0 0
type t6 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t7 INT32 4 4 0 comparable,named "int32" "int32"
type t8 UINT8 1 1 0 comparable,named "abi.FuncID" "internal/abi.FuncID"
type t9 UINT8 1 1 0 comparable,named "abi.FuncFlag" "internal/abi.FuncFlag"
type t11 UINT8 1 1 0 comparable,named "byte" "uint8"
type t10 ARRAY 1 1 0 comparable "[1]byte" "[1]uint8" t11 1
type t12 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t3 STRUCT 44 4 0 notinheap,comparable,named "_func" "runtime._func" 15
field 0 "NotInHeap" t4 0 1
field 1 "entryOff" t6 0 0
field 2 "nameOff" t7 4 0
field 3 "args" t7 8 0
field 4 "deferreturn" t6 12 0
field 5 "pcsp" t6 16 0
field 6 "pcfile" t6 20 0
field 7 "pcln" t6 24 0
field 8 "npcdata" t6 28 0
field 9 "cuOffset" t6 32 0
field 10 "startLine" t7 36 0
field 11 "funcID" t8 40 0
field 12 "flag" t9 41 0
field 13 "_" t10 42 0
field 14 "nfuncdata" t12 43 0
type t2 PTR 8 8 0 comparable "*_func" "*runtime._func" t3
type t13 BOOL 1 1 0 comparable,named "bool" "bool"
type t1 FUNC 8 8 8 hasptr,direct "method(*_func) func() bool" "method(*runtime._func) func() bool" 1 0 1
field 0 "f" t2 ? 0
field 1 "" t13 ? 0
aux a2 sym "runtime.(*_func).isInlined" "runtime.(*_func).isInlined" 1 - 0 - - - - 0
posbase p40 "runtime/symtab.go" 1 1 -1
aux a3 name "f" "f" PPARAM t2 0 1 used p40:887:7:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t13 0 1 - p40:887:29:0:0
aux a1 call "AuxCall{runtime.(*_func).isInlined}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t13 a4 0 -1
type t14 INT8 1 1 0 comparable,named "int8" "int8"
type t15 INT16 2 2 0 comparable,named "int16" "int16"
type t16 INT64 8 8 0 comparable,named "int64" "int64"
type t17 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t18 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t19 INT 8 8 0 comparable,named "int" "int"
type t20 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t21 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t22 UINT 8 8 0 comparable,named "uint" "uint"
type t23 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t24 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t25 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t12
type t26 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t7
type t27 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t6
type t28 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t19
type t29 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t23
type t30 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t20
type t31 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t21
type t32 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t25
type t33 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t34 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t35 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t36 SSA ? ? ? - "mem" ""
type t37 SSA ? ? ? - "flags" ""
type t38 SSA ? ? ? - "void" ""
type t39 SSA 16 8 ? - "int128" ""
type t40 RESULTS ? ? ? - "mem" "" 1 t36
type t41 PTR 8 8 8 hasptr,direct,comparable "**_func" "**runtime._func" t2
type t42 PTR 8 8 8 hasptr,direct,comparable "*bool" "*bool" t13
type t43 RESULTS ? ? ? - "bool,mem" "" 2 t13,t36
slot s1 a3 t2 0 - 0
f b1 t1 a1 13 1
typs Bool=t13,Int8=t14,Int16=t15,Int32=t7,Int64=t16,UInt8=t12,UInt16=t17,UInt32=t6,UInt64=t18,Int=t19,Float32=t20,Float64=t21,UInt=t22,Uintptr=t23,String=t24,BytePtr=t25,Int32Ptr=t26,UInt32Ptr=t27,IntPtr=t28,UintptrPtr=t29,Float32Ptr=t30,Float64Ptr=t31,BytePtrPtr=t32,Complex64=t33,Complex128=t34,UnsafePtr=t35,Mem=t36,Flags=t37,Void=t38,Int128=t39,ResultMem=t40
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 5 -
v v2 SP t23 0 - p0:0:0:0:0 2 -
v v3 SB t23 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t41 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t42 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v7 ConstBool t13 0 - p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p40:888:10:0:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11,0=v7
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 5 -
v v2 SP t23 0 - p0:0:0:0:0 2 -
v v3 SB t23 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t41 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t42 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v7 ConstBool t13 0 - p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11,0=v7
freev -
freeb -
cache postorder b1
cache linestarts 40:888:888
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 5 -
v v2 SP t23 0 - p0:0:0:0:0 2 -
v v3 SB t23 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t41 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t42 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v7 ConstBool t13 0 - p0:0:0:0:0 0 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11,0=v7
freev -
freeb -
cache postorder b1
cache linestarts 40:888:888
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 40:888:888
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 40:888:888
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 40:888:888
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 40:888:888
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 40:888:888
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 40:888:888
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 40:888:888
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p40:887:6:2:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "f+0" a3 0
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v7 SB t23 0 - p0:0:0:0:0 0 -
v v5 SP t23 0 - p0:0:0:0:0 2 -
v v4 OffPtr t41 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t42 0 a4 p40:888:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11,0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v7 SB t23 0 - p0:0:0:0:0 0 -
v v5 SP t23 0 - p0:0:0:0:0 2 -
v v4 OffPtr t41 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t42 0 a4 p40:888:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11,0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v7 SB t23 0 - p0:0:0:0:0 0 -
v v5 SP t23 0 - p0:0:0:0:0 2 -
v v4 OffPtr t41 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t42 0 a4 p40:888:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11,0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v7 SB t23 0 - p0:0:0:0:0 0 -
v v5 SP t23 0 - p0:0:0:0:0 2 -
v v4 OffPtr t41 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t42 0 a4 p40:888:2:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11,0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v11 Const32 t6 -1 - p0:0:0:0:0 1 -
v v8 NilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v9 OffPtr t27 0 - p40:888:10:0:0 1 v8
v v10 Load t6 0 - p40:888:10:0:0 1 v9,v1
v v12 Eq32 t13 0 - p40:888:20:0:0 1 v10,v11
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v11
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 40:888:888
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p40:888:10:1:0 1 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v8,v1
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 2 -
v v1 InitMem t36 0 - p0:0:0:0:0 3 -
v v8 ARM64LoweredNilCheck t38 0 - p40:888:10:1:0 0 v6,v1
v v10 ARM64MOVWUload t6 0 - p40:888:10:0:0 1 v6,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v1 InitMem t36 0 - p0:0:0:0:0 2 -
v v10 ARM64MOVWUload t6 0 - p40:888:10:1:0 1 v6,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v1 InitMem t36 0 - p0:0:0:0:0 2 -
v v10 ARM64MOVWUload t6 0 - p40:888:10:1:0 1 v6,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v11,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.(*_func).isInlined}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t13 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v1 InitMem t36 0 - p0:0:0:0:0 2 -
v v10 ARM64MOVWUload t6 0 - p40:888:10:1:0 1 v6,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v5,v7,v9,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
fstate scheduled,laidout
regalloc 14 v6:R0,v10:R1,v12:R0,v13:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v1 InitMem t36 0 - p0:0:0:0:0 2 -
v v10 ARM64MOVWUload t6 0 - p40:888:10:1:0 1 v6,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v5,v7,v9,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
fstate scheduled,laidout
regalloc 14 v6:R0,v10:R1,v12:R0,v13:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 13 1
b b1 Ret p40:888:23:1:0 0 0 - v13 - -
v v6 ArgIntReg t2 0 a5 p40:888:23:1:0 1 -
v v1 InitMem t36 0 - p0:0:0:0:0 2 -
v v10 ARM64MOVWUload t6 0 - p40:888:10:1:0 1 v6,v1
v v3 ARM64CMNWconst t37 1 - p40:888:20:0:0 1 v10
v v12 ARM64Equal t13 0 - p40:888:20:0:0 1 v3
v v13 MakeResult t43 0 - p40:888:2:0:0 1 v12,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v5,v7,v9,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 40:888:888
fstate scheduled,laidout
regalloc 14 v6:R0,v10:R1,v12:R0,v13:[]
dcllen 2
end
frontend
end
ptrcache t3,t6,t7,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t29,t32,t33,t34,t35
typelink t11=t12,t36=t40
typeorder t14,t11=t12,t8,t9,t15,t17,t7,t6,t16,t18,t19,t22,t23,t33,t34,t20,t21,t13,t25,t26,t27,t28,t29,t30,t31,t42,t32,t41,t2,t1,t10,t5,t3,t4,t24,t35,t36,t38,t37,t39,t40,t43
eof
"#

/-- `std/std/runtime/(*_func).isInlined,1.prog` (quick-v10). -/
def fProgC : String := r#"gofv-prog 3
pkg "runtime"
func "(*_func).isInlined" 1
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
type t1 8 8 0 0 - "*_func"
name n1 "f" PPARAM t1 1 "runtime.f" 0 a3
type t2 1 1 0 0 - "bool"
name n2 "~r0" PPARAMOUT t2 1 "runtime.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p40 "runtime/symtab.go" 1 1 -1 39 "runtime/symtab.go" "runtime/symtab.go" 1 1
sym y1 "runtime.(*_func).isInlined" 1
curfn p40:887:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 887 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.(*_func).isInlined.arginfo1" 0
sym y4 "runtime.(*_func).isInlined.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p40:887:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p40:887:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p40:887:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p40:887:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p40:887:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p40:887:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p40:888:10:1:0
p 7 7 0 0 0 - MOVWU 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p40:888:10:1:0
p 8 8 0 0 0 - CMNW 0 CONST/0/0/0/NONE/0/1/-/- 8193 - _ 0 0 p40:888:20:2:0
p 9 9 0 0 0 - CSET 0 SPECIAL/0/0/0/NONE/0/128/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p40:888:20:2:0
p 10 10 0 0 0 - RET 0 _ 0 - _ 0 0 p40:888:23:2:0
p 11 11 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 887 201080
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
dbgloc 0 1:-10000:1:12:50
dbgregout n2
dbgpc 1:12:10
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p40:887:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p40:887:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p40:887:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p40:887:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p40:887:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p40:887:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p40:888:10:1:0
p 7 0 0 0 392 - MOVWU 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p40:888:10:1:0
p 8 4 0 0 96 - CMNW 0 CONST/0/0/0/NONE/17/1/-/- 8193 - NONE/0/0/0/NONE/1/0/-/- 0 0 p40:888:20:2:0
p 9 8 0 0 103 - CSET 0 SPECIAL/0/0/0/NONE/11/128/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p40:888:20:2:0
p 10 12 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p40:888:23:2:0
fn y1 8 0 0 0 887 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 16 0 010040b93f040031e0179f9ac0035fd6 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 39
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 3 1 28000 010400 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040400 0
data y9 SRODATA 3 1 28000 020400 0
data y10 SRODATA 3 1 28000 500400 0
data y11 SRODATA 4 1 28000 f20d0400 0
data y12 SRODATA 3 1 28000 000400 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "go:info.runtime.(*_func).isInlined$abstract" 0
sym y17 "" 0
sym y18 "go:info.*runtime._func" 0
sym y19 "go:info.bool" 0
sym y20 "type:bool" 0
dwfn y13 y14 y15 y16 y17 "runtime.(*_func).isInlined" 39:887 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y16 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime._func" 0 0 1 p40:887:7:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "bool" 0 0 1 p40:887:29:0:0
var 0 0 "f" 5 1 0 0 0 8 y18 "runtime/symtab.go" 887 7 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y19 "runtime/symtab.go" 887 29 0 1 0 0 -
scope 0 0 - 0,1
dieref y13 3 y16 0
dieoff y16 0:32
data y13 SDWARFFCN 33 0 0 0600000000000010019c2900000000000000002e7e72300001f706000000000000 6
reloc 0 0 R_USETYPE 0 y20
reloc 1 4 R_DWARFSECREF 0 y16
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y16
reloc 15 4 R_DWARFSECREF 0 y14
reloc 27 4 R_DWARFSECREF 0 y19
data y14 SDWARFLOC 9 0 0 01000004000c015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 24 0 0 0009020000000000000000042803f206140637020c000101 1
reloc 3 8 R_ADDR 0 y1
data y16 SDWARFABSFCN 41 0 1 0572756e74696d652e282a5f66756e63292e6973496e6c696e65640001f70601226600000000000000 1
reloc 36 4 R_DWARFSECREF 0 y18
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stInC : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsaC fProgC

def lcC : LocCtx :=
  match stInC with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

def psC : Array GoFV.Asm.Prog :=
  match stInC with
  | .ok x => x.2.1
  | .error _ => #[]

def bsC : ID → Option Nat :=
  match stInC with
  | .ok x => x.2.2.1
  | .error _ => fun _ => none

def gC : G2In :=
  match stInC with
  | .ok x => x.2.2.2
  | .error _ => { syms := #[], slotOp := fun _ => none, stksize := 0 }

/-- The PC table `checkG33` gives (`b1`: one entry per value `v6`, `v1`, `v10`, `v3`, `v12`, `v13`, then the `RET`). -/
def tabC : PcTab := [(1, [5, 5, 5, 8, 9, 10, 10])]

/-- The class table `checkG33` gives. -/
def ktC : KTab := (match checkG33 lcC psC bsC gC with
  | .ok (_, k) => k
  | .error _ => [])

def blkC : Block := (lcC.ctx.f.block? 1).getD default

def valC (n : ID) : Value := (lcC.ctx.f.value? n).getD default

def LC : Link := Lof psC

def EC : MatchEnv := Eof lcC psC tabC

/-- The `runLoc` state before `v3`: the 32-bit `f.entryOff = 0xffffffff` in `R1`, every other register `poison`. -/
def s0C : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 1 then .int .w32 0xffffffff else .poison,
    flags := .poison, slots := [], mem := .mem mem0 }

/-- The machine before `v3`: `X1 = 0xffffffff`, the activation's `g` and `FP`, the PC of `v3`, a
zero memory. -/
def m0C : MState :=
  { x := fun k => if k = 1 then 0xffffffff else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := EC.pcOf 1 3, mem := fun _ => 0 }

/-- The flags value has `Z` set. -/
def isZC : Val → Bool
  | .agg [_, .bool true, _, _, _] => true
  | _ => false

theorem isZC_spec {f : Val} (h : isZC f = true) :
    ∃ n c v g', f = .agg [n, .bool true, c, v, g'] := by
  unfold isZC at h
  split at h
  · exact ⟨_, _, _, _, rfl⟩
  · cases h

/-- What compiled evaluation checks on `isInlined`: it holds an arm64 op, `checkG33` accepts it
with `tabC` and `ktC` and `checkG31` does not; it accesses no frame variable and has no home slot;
`b1` holds `v3` (`CMNWconst`) at index 3; `R1` has class 32 before it, where G31's table is
`[(1, 32, false)]`; `stepLoc` runs `v3` from `s0C` to flags with `Z` set. -/
def gFactsC : Bool :=
  lcC.ctx.f.lowered &&
    (checkG33 lcC psC bsC gC).toOption == some (tabC, ktC) &&
    (checkG31 lcC psC bsC gC).toOption.isNone &&
    (accessedVars lcC).isEmpty && (homeSlots lcC).isEmpty &&
    lcC.ctx.f.blocks.toList.contains 1 && (lcC.ctx.f.block? 1).isSome &&
    (lcC.ctx.f.value? 3).isSome && blkC.values[3]? == some 3 &&
    (valC 3).op == .ARM64CMNWconst &&
    (kAt lcC ktC 1 blkC 3).get 1 == some 32 &&
    uL31 lcC (uIn lcC 1) blkC 3 == [(1, 32, false)] &&
    GenG1.okThen (stepLoc GenG2.env lcC s0C (valC 3)) fun s1 => isZC s1.flags

/-! ## The facts -/

/-- What compiled evaluation checks: `gFactsU` and `gFactsC`. -/
def gFacts : Bool := gFactsU && gFactsC

theorem g33b_facts : gFacts = true := by
  native_decide

theorem gFactsU_true : gFactsU = true := by
  have h := g33b_facts
  simp only [gFacts, Bool.and_eq_true] at h
  exact h.1

theorem gFactsC_true : gFactsC = true := by
  have h := g33b_facts
  simp only [gFacts, Bool.and_eq_true] at h
  exact h.2

/-! ## `UBFIZ` -/

/-- The facts of `gFactsU` as hypotheses. -/
theorem factsU :
    lcU.ctx.f.lowered = true ∧ checkG33 lcU psU bsU gU = .ok (tabU, ktU) ∧
      (checkG31 lcU psU bsU gU).toOption = none ∧
      (accessedVars lcU).isEmpty = true ∧ (homeSlots lcU).isEmpty = true ∧
      2 ∈ lcU.ctx.f.blocks.toList ∧ lcU.ctx.f.block? 2 = some blkU ∧
      lcU.ctx.f.value? 13 = some (valU 13) ∧ blkU.values[3]? = some 13 ∧
      (valU 13).op = .ARM64UBFIZ ∧ (kAt lcU ktU 2 blkU 3).get 1 = some 16 ∧
      uL31 lcU (uIn lcU 2) blkU 3 = [(1, 16, false)] ∧
      GenG1.okThen (stepLoc GenG2.env lcU s0U (valU 13)) (fun s1 => isResU s1.regs[1]?) = true := by
  have hf := gFactsU_true
  simp only [gFactsU, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h31, hav, hsl, hmb, hbs, hvs, hi, hop, hk, hu, hrun⟩ := hf
  refine ⟨hl, ?_, h31, hav, hsl, hmb, ?_, ?_, hi, hop, hk, hu, hrun⟩
  · revert hres; cases checkG33 lcU psU bsU gU <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blkU, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [valU, hv]

theorem s0U_regs {r : Nat} {x : Val} (h : s0U.regs[r]? = some x) :
    (r = 1 ∧ x = .int .w16 0xbeef) ∨ x = .poison := by
  simp only [s0U, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0U : LocMatch EU s0U 2 3 m0U where
  regs := by
    intro r v hv
    rcases s0U_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show BitVec.setWidth 16 (m0U.x 1) = 0xbeef
      decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0U] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0U, EU, Eof]; decide,
    by simp only [MState.word, readMem, m0U, EU, Eof]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g33Inv0U (hk : (kAt lcU ktU 2 blkU 3).get 1 = some 16) :
    G3Inv EU lcU (kAt lcU ktU 2 blkU 3) s0U where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0U_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [hk] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0U] at h

/-- `m0U` keeps G31's table before `v13`: `X1` is zero-extended from 16 bits. -/
theorem uokl0U : UOKL m0U [(1, 16, false)] := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  show ∀ k : Nat, k < 31 → objX? 1 = some (BitVec.ofNat 5 k) →
    ExtOK (m0U.x (BitVec.ofNat 5 k)) 16 false
  unfold ExtOK
  decide

/-- The per-value premises of `v13`: none apply. -/
theorem preU {s : LocState} (hop : (valU 13).op = .ARM64UBFIZ) : G14Pre lcU s (valU 13) := by
  have hne : ∀ o : Op, o ≠ .ARM64UBFIZ → (valU 13).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G33's `UBFIZ` on `runtime.(*mspan).pinnerBitSize`**: from the state before `v13` with the
16-bit `s.nelems = 0xbeef` in `R1`, on a machine whose `X1 = 0xbeef` is zero-extended from 16 bits
(G31's table), `g33_value` runs `UBFIZ $1, R1, $16, R1` (`v13`, `uintptr(s.nelems)*2`): `runLoc`'s
`R1` holds the 64-bit `0x17dde` and the machine state, related to it before `v18` under an
activation extending `EU` that is again a `G28Env`, has `X1 = 0x17dde`. -/
theorem genG33_ubfiz_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lcU s0U (valU 13) = .ok s1 ∧
      s1.regs[1]? = some (.int .w64 0x17dde) ∧
      EU.Extends E1 ∧ G28Env lcU gU LU psU 0 tabU E1 ∧
      PStar GenG2.H0 LU psU.toList 0 m0U m1 ∧
      LocMatch E1 s1 2 4 m1 ∧ m1.x 1 = 0x17dde := by
  obtain ⟨hl, hc, -, hav, hsl, hmb, hb, hv, hi, hop, hk, hu, hrun⟩ := factsU
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hE : G28Env lcU gU LU psU 0 tabU EU := envOf hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64UBFIZ → (valU 13).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g33_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hmb hb hi hv (by rw [hop]; rfl) locMatch0U (g33Inv0U hk)
    (by rw [hu]; exact uokl0U) (preU hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  have hr1' := isResU_spec hr1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  exact ⟨s1, E1, m1, hs1, hr1', hx1, hE1, hp1, hm1',
    valRel_i64 hA ((hm1'.regs 1 _ hr1').1 1 rfl)⟩

/-! ## `CMNWconst` -/

/-- The facts of `gFactsC` as hypotheses. -/
theorem factsC :
    lcC.ctx.f.lowered = true ∧ checkG33 lcC psC bsC gC = .ok (tabC, ktC) ∧
      (checkG31 lcC psC bsC gC).toOption = none ∧
      (accessedVars lcC).isEmpty = true ∧ (homeSlots lcC).isEmpty = true ∧
      1 ∈ lcC.ctx.f.blocks.toList ∧ lcC.ctx.f.block? 1 = some blkC ∧
      lcC.ctx.f.value? 3 = some (valC 3) ∧ blkC.values[3]? = some 3 ∧
      (valC 3).op = .ARM64CMNWconst ∧ (kAt lcC ktC 1 blkC 3).get 1 = some 32 ∧
      uL31 lcC (uIn lcC 1) blkC 3 = [(1, 32, false)] ∧
      GenG1.okThen (stepLoc GenG2.env lcC s0C (valC 3)) (fun s1 => isZC s1.flags) = true := by
  have hf := gFactsC_true
  simp only [gFactsC, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h31, hav, hsl, hmb, hbs, hvs, hi, hop, hk, hu, hrun⟩ := hf
  refine ⟨hl, ?_, h31, hav, hsl, hmb, ?_, ?_, hi, hop, hk, hu, hrun⟩
  · revert hres; cases checkG33 lcC psC bsC gC <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blkC, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [valC, hv]

theorem s0C_regs {r : Nat} {x : Val} (h : s0C.regs[r]? = some x) :
    (r = 1 ∧ x = .int .w32 0xffffffff) ∨ x = .poison := by
  simp only [s0C, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0C : LocMatch EC s0C 1 3 m0C where
  regs := by
    intro r v hv
    rcases s0C_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show BitVec.setWidth 32 (m0C.x 1) = 0xffffffff
      decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0C] at h
  mem := ⟨mem0, rfl, memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0C, EC, Eof]; decide,
    by simp only [MState.word, readMem, m0C, EC, Eof]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g33Inv0C (hk : (kAt lcC ktC 1 blkC 3).get 1 = some 32) :
    G3Inv EC lcC (kAt lcC ktC 1 blkC 3) s0C where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem0, rfl, by simp [KeysNodup, mem0],
      fun b al a h => by simp [mem0] at h⟩
    rcases s0C_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [hk] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0C] at h

/-- `m0C` keeps G31's table before `v3`: `X1` is zero-extended from 32 bits. -/
theorem uokl0C : UOKL m0C [(1, 32, false)] := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  show ∀ k : Nat, k < 31 → objX? 1 = some (BitVec.ofNat 5 k) →
    ExtOK (m0C.x (BitVec.ofNat 5 k)) 32 false
  unfold ExtOK
  decide

/-- The per-value premises of `v3`: none apply. -/
theorem preC {s : LocState} (hop : (valC 3).op = .ARM64CMNWconst) : G14Pre lcC s (valC 3) := by
  have hne : ∀ o : Op, o ≠ .ARM64CMNWconst → (valC 3).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G33's `CMNWconst` on `runtime.(*_func).isInlined`**: from the state before `v3` with the
32-bit `f.entryOff = 0xffffffff` in `R1`, on a machine whose `X1 = 0xffffffff` is zero-extended from
32 bits (G31's table), `g33_value` runs `CMNW $1, R1` (`v3`, `f.entryOff == ^uint32(0)`): `runLoc`'s
flags have `Z` set, and the machine state, related to it before `v12` under an activation
extending `EC` that is again a `G28Env`, has its `Z` flag set. -/
theorem genG33_cmnw_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env lcC s0C (valC 3) = .ok s1 ∧ isZC s1.flags = true ∧
      EC.Extends E1 ∧ G28Env lcC gC LC psC 0 tabC E1 ∧
      PStar GenG2.H0 LC psC.toList 0 m0C m1 ∧
      LocMatch E1 s1 1 4 m1 ∧ m1.nzcv.z = true := by
  obtain ⟨hl, hc, -, hav, hsl, hmb, hb, hv, hi, hop, hk, hu, hrun⟩ := factsC
  obtain ⟨s1, hs1, hr1⟩ := GenG1.okThen_spec hrun
  have hE : G28Env lcC gC LC psC 0 tabC EC := envOf hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64CMNWconst → (valC 3).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g33_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hmb hb hi hv (by rw [hop]; rfl) locMatch0C (g33Inv0C hk)
    (by rw [hu]; exact uokl0C) (preC hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  obtain ⟨n, c, v, g', hf⟩ := isZC_spec hr1
  have hfl := hm1'.flags
  rw [hf] at hfl
  exact ⟨s1, E1, m1, hs1, hr1, hx1, hE1, hp1, hm1', hfl.2.1.symm⟩

end GoFV.Proof.Witness.GenG33b
