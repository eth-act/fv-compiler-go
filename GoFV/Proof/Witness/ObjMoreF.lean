import GoFV.Proof.Witness.ObjFrame

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: the morestack tail of `math.Tan`, which spills `F0` (`obj_entry`, `MoreStep`)

`std/std/math/Tan,1.prog` of the corpus (`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded
verbatim as `tanProg`), run through the assembler port and the validator as `obj-check` does
(`GoFVTest/ObjCheck.lean`, `checkFile`), as `Witness/ObjFrame.lean` does for `testInts`.
`math.Tan` is framed (`autosize = 32`, it calls `math.tan`), takes its argument in `F0` and has
the small stack check; its morestack tail spills `F0` with `FMOVD F0, 8(RSP)` and reloads it with
`FMOVD 8(RSP), F0`:

```
 0 MOVD 16(R28), R16    12 MOVD.W R30, -32(RSP)   24 CALL math.tan      40 FMOVD F0, 8(RSP)
 4 CMP R16, RSP         16 MOVD R29, -8(RSP)      28 epilogue, RET      44 MOVD R30, R3
 8 BLS 40               20 SUB $8, RSP, R29                             48 CALL runtime.morestack_noctxt
                                                                        52 FMOVD 8(RSP), F0
                                                                        56 JMP 0
```

By compiled evaluation (`native_decide`, as `ObjFrame.obj_facts`; `tan_facts`), `checkObj`
accepts it with the frame size 32, a stack check reading `16(g)` with the tail at 40, the body at
24; `tailPlan` is the one slot `⟨0, 8, 8, false, true⟩` (`V0`'s `D` part at `8(SP)`); `linkCode`
links it as `ObjFrame` does; the tail calls symbol 6, which has no code. From the entry `s0m`
(`F0 = π`, the stack check failing: `stackguard0` all ones) under the hook `msHookV`, which
clears the guard and clobbers every vector register, `obj_entry` runs the morestack path and the
prologue to the body, and `MoreStep`'s reload of `V0` (`vreloadVal 8`) gives back `π`
(`objMoreF_witness`). `fvalRel_vreloadVal_witness` instantiates `fvalRel_vreloadVal`.
-/

namespace GoFV.Proof.Witness.ObjMoreF

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj GoFV.Proof.Obj
open GoFV.SSA.Sem (MStar)
open GoFV.Proof.Witness.ObjFrame (isOk getOk eq_getOk)

/-- `std/std/math/Tan,1.prog` of quick-v10, verbatim. -/
def tanProg : String := r#"gofv-prog 3
pkg "math"
func "Tan" 1
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
type t1 8 8 0 0 - "float64"
name n1 "x" PPARAM t1 1 "math.x" 0 a3
name n2 "~r0" PPARAMOUT t1 1 "math.~r0" 0 a4
name n3 ".autotmp_2" PAUTO t1 3 "math..autotmp_2" 0 -
in n1 0 used
in n2 0 outregs
in n3 0 used,autotmp
out n1 0 used
opt n3 0 autotmp
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p8 "math/tan.go" 1 1 -1 7 "math/tan.go" "math/tan.go" 1 1
sym y1 "math.Tan" 1
curfn p8:83:6:0:0 0 0
regargs 8224:0:t1
text y1 0 0 0 0 83 200080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "math.Tan.arginfo1" 0
sym y4 "math.Tan.argliveinfo" 0
sym y5 "math.tan" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p8:83:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p8:83:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p8:83:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p8:83:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p8:83:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p8:83:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p8:87:12:1:0
p 7 7 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p8:87:12:1:0
p 8 8 0 0 0 - RET 0 _ 0 - _ 0 0 p8:87:2:2:0
p 9 9 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 83 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8224 0 FMOVD FMOVD
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:1:8:9040
dbgregout n2
dbgpc 1:8:8
end
asm
sym y6 "runtime.morestack_noctxt" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i8 0 0 p8:83:6:0:0
p 10 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p8:83:6:0:0
p 11 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p8:83:6:0:0
p 12 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p8:83:6:0:0
p 13 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@22 0 0 p8:83:6:0:0
p 14 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p8:83:6:0:0
p 15 12 32 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-32/-/- 0 0 p8:83:6:0:1
p 16 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p8:83:6:0:0
p 17 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p8:83:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p8:83:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p8:83:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p8:83:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p8:83:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p8:83:6:2:0
p 6 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p8:87:12:1:0
p 7 24 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y5/- 0 0 p8:87:12:1:0
p 8 28 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p8:87:2:2:0
p 18 32 -32 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/32/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p8:87:2:2:0
p 19 36 32 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p8:87:2:2:0
p 20 40 -32 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p8:87:2:2:0
p 21 40 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p8:83:6:0:0
p 22 40 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p8:83:6:0:0
p 23 40 0 0 144 - FMOVD 0 REG/8224/0/0/NONE/5/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p8:83:6:0:0
p 24 44 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p8:83:6:0:0
p 25 48 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y6/- 0 0 p8:83:6:0:0
p 26 52 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p8:83:6:0:0
p 27 52 0 0 157 - FMOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8224/0/0/NONE/5/0/-/- 0 0 p8:83:6:0:0
p 28 56 32 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@10 0 0 p8:83:6:0:0
fn y1 8 24 0 0 83 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8224 0 FMOVD FMOVD
funcaux y2 y2 - - y3 y4 -
text 64 0 900b40f9ff6330eb09010054fe0f1ef8fd831ff8fd2300d100000094fd835ff8fe0742f8c0035fd6e00700fde3031eaa00000094e00740fdf2ffff1700000000 2
reloc 24 4 R_CALLARM64 0 y5
reloc 48 4 R_CALLARM64 0 y6
pcln y11 y12 y13 y14 y7,y8,y9,y10 y2,y2,_,_,_,y3,y4
usedfiles 7
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y7 SRODATA 11 1 28000 0001010202070103020300 0
data y8 SRODATA 7 1 28000 00060204010600 0
data y9 SRODATA 0 1 28000 - 0
data y10 SRODATA 5 1 28000 0006040a00 0
data y11 SRODATA 7 1 28000 020440053f0700 0
data y12 SRODATA 3 1 28000 101000 0
data y13 SRODATA 8 1 28000 a801060804070600 0
data y14 SRODATA 3 1 28000 001000 0
end
dwarf
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "go:info.float64" 0
sym y20 "type:float64" 0
dwfn y15 y16 y17 - y18 "math.Tan" 7:83 1 0 1 177
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "float64" 0 0 1 p8:83:10:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "float64" 0 0 1 p8:87:12:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "float64" 0 0 1 p8:83:21:0:0
var 0 0 "x" 5 1 0 0 0 8 y19 "math/tan.go" 83 10 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y19 "math/tan.go" 83 21 0 1 0 0 -
scope 0 0 - 0,1
data y15 SDWARFFCN 47 0 0 036d6174682e54616e00000040019c0800000053012d7800005300000000000000002e7e7230000153000000000000 5
reloc 0 0 R_USETYPE 0 y20
reloc 10 2 R_DWTXTADDR_U2 0 y1
reloc 26 4 R_DWARFSECREF 0 y19
reloc 30 4 R_DWARFSECREF 0 y16
reloc 41 4 R_DWARFSECREF 0 y19
data y16 SDWARFLOC 10 0 0 01000004001c02904000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y17 SDWARFRANGE 0 0 0 - 0
data y18 SDWARFLINES 29 0 0 0009020000000000000000040803cd00140a878b063706830218000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The P0 Progs, the spills and the port's output of `math.Tan` (as `obj-check`). -/
def objIn : Except String (Array Prog × Array Spill × ObjIn) := do
  let pf ← parseProgFile tanProg.toUTF8
  let out ← flush pf
  return (pf.prog0.progs, pf.prog0.fn.spills,
    { text := out.st.textP, relocs := out.st.textR, progs := out.progs })

def ps : Array Prog :=
  match objIn with
  | .ok x => x.1
  | .error _ => #[]

def spills : Array Spill :=
  match objIn with
  | .ok x => x.2.1
  | .error _ => #[]

def obj : ObjIn :=
  match objIn with
  | .ok x => x.2.2
  | .error _ => ⟨ByteArray.empty, #[], #[]⟩

/-- What `checkObj` returns on `math.Tan`. -/
def tab : Tab := getOk (checkObj ps spills obj)

def base : BitVec 64 := 0x10000

def sym : Nat → BitVec 64 := fun _ => 0x100000

/-- The caller's return address. -/
def retM : BitVec 64 := 0x40

/-- The linked code. -/
def code : Code := getOk (linkCode base sym obj.text obj.relocs.toList)

def sp0 : BitVec 64 := 0x7fff0000

/-- π as a `float64`. -/
def pi64 : BitVec 128 := 0x400921fb54442d18

/-- The entry with a full stack: PC at `base`, `g = 0x9000`, `R29 = SP − 8`, `LR = retM`,
`F0 = π`, `stackguard0` (`16(g)`) all ones, so the stack check fails. -/
def s0m : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then sp0 - 8 else if k = 30 then retM else 0,
    sp := sp0, v := fun k => if k = 0 then pi64 else 0, nzcv := ⟨false, false, false, false⟩,
    pc := base, mem := fun a => if InWord (0x9000 + BitVec.ofNat 64 16) a then 0xff else 0 }

/-- The slot plan of `math.Tan`: `V0`'s `D` part at `8(SP)`. -/
def plan : List TailSlot := [⟨0, 8, 8, false, true⟩]

/-- What compiled evaluation checks: `checkObj` accepts `math.Tan` (frame 32, a stack check
ending at 12 with the morestack tail at 40 reading `16(g)`, body at 24), `linkCode` succeeds, the
text fits, `retM` has no code, the tail calls symbol 6 (`runtime.morestack_noctxt`), which has no
code, and spills `F0` to `8(RSP)`. -/
def tanFacts : Bool :=
  isOk (checkObj ps spills obj) && tab.autosize == 32 && tab.check == some (12, 40, 16) &&
    tab.offs[0]! == 24 && isOk (linkCode base sym obj.text obj.relocs.toList) &&
    decide (obj.text.size ≤ 2 ^ 64) && code retM == none &&
    tailCall obj.text obj.relocs.toList 40 == some (6, 0) &&
    code (sym 6 + BitVec.ofInt 64 0) == none && isOk (tailPlan spills.toList) &&
    getOk (tailPlan spills.toList) == plan

theorem tan_facts : tanFacts = true := by
  native_decide

/-- The facts of `tan_facts` as hypotheses. -/
theorem facts :
    checkObj ps spills obj = .ok tab ∧ tab.autosize = 32 ∧ tab.check = some (12, 40, 16) ∧
      tab.offs[0]! = 24 ∧ linkCode base sym obj.text obj.relocs.toList = .ok code ∧
      obj.text.size ≤ 2 ^ 64 ∧ code retM = none ∧
      tailCall obj.text obj.relocs.toList 40 = some (6, 0) ∧
      code (sym 6 + BitVec.ofInt 64 0) = none ∧ tailPlan spills.toList = .ok plan := by
  have hf := tan_facts
  simp only [tanFacts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, haz⟩, hchk⟩, h0⟩, hl⟩, hsz⟩, hret⟩, htc⟩, hcode⟩, hplok⟩, hpl⟩ := hf
  exact ⟨eq_getOk hc, haz, hchk, h0, eq_getOk hl, hsz, hret, htc, hcode,
    by rw [eq_getOk hplok, hpl]⟩

/-- `s0m` is a call of `math.Tan` at `base` with 4096 bytes of stack below `SP`. -/
theorem machEntry_m : MachEntry code base 4096 s0m where
  pc := rfl
  spAlign := by decide
  room := by decide
  lrOutside := by
    obtain ⟨-, -, -, -, -, -, hret, -⟩ := facts
    exact hret
  gOutside := by decide
  fp := by decide

/-- A `runtime.morestack` for the witness: it returns to `X30` with `X30` set to `R3`, every other
general register and the memory kept but `stackguard0` (`16(g)`), which it clears, and every
vector register clobbered (all ones). -/
def msHookV : Hooks := ⟨fun s => some (.ret
  { s with
    pc := s.x 30
    x := fun i => if i = 30 then s.x 3 else s.x i
    v := fun _ => -1
    mem := fun a => if InWord (s.x 28 + BitVec.ofNat 64 16) a then 0 else s.mem a })⟩

/-- `msHookV` meets the contract of `runtime.morestack` for `math.Tan` entered with
`g = 0x9000` and `SP = 0x7fff0000`. -/
theorem msHookV_ok {s : MState} (hg : s.x 28 = 0x9000) (hsp : s.sp = sp0) :
    MorestackOK msHookV code retM (sym 6 + BitVec.ofInt 64 0) 32 16 s := by
  obtain ⟨-, -, -, -, -, -, -, -, hcode, -⟩ := facts
  refine ⟨hcode, by decide, fun t hpc hsp' h28 _ hfail => ⟨_, rfl, rfl, rfl, by simp, by simp,
    by simp, by simp, fun a ha => by show (if _ then _ else _) = _; simp only [ha, ↓reduceIte],
    ?_⟩⟩
  unfold CheckPasses at hfail
  unfold guardOf
  simp only [show (32 : Int) ≤ 128 by decide, ↓reduceIte, hsp', hsp, Nat.not_lt] at hfail
  have h0 : (readMem (fun a => if InWord (t.x 28 + BitVec.ofNat 64 16) a then 0 else t.mem a)
      (t.x 28 + BitVec.ofNat 64 16) 8).toNat = 0 := by
    apply GoFV.Proof.Gen.readMem_of_bytes _ 8 _ 0 (by decide)
    intro j hj
    have hA : (t.x 28 + BitVec.ofNat 64 16).toNat = 0x9010 := by rw [h28, hg]; decide
    have hw : InWord (t.x 28 + BitVec.ofNat 64 16) (t.x 28 + BitVec.ofNat 64 16 + BitVec.ofNat 64 j) := by
      unfold InWord
      rw [BitVec.toNat_add (t.x 28 + BitVec.ofNat 64 16), hA, BitVec.toNat_ofNat]
      omega
    simp only [hw, ↓reduceIte, Nat.zero_div, Nat.zero_mod]
    rfl
  show (readMem (fun a => if InWord (t.x 28 + BitVec.ofNat 64 16) a then 0 else t.mem a)
    (t.x 28 + BitVec.ofNat 64 16) 8).toNat < _
  rw [h0]
  have : sp0.toNat = 0x7fff0000 := rfl
  omega

/-- `math.Tan`'s spill slot `8(RSP)` lies below `2^64` and apart from `g`. -/
theorem tailSep : TailSep spills.toList s0m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hpl⟩ := facts
  intro sl h q hq
  rw [hpl] at h
  cases h
  simp only [plan, List.mem_singleton] at hq
  subst hq
  decide

/-- **The morestack path of `math.Tan`, whose tail spills `F0`**: from the entry `s0m`, whose
stack check fails, through the morestack tail (`FMOVD F0, 8(RSP)`, `msHookV` clears the guard and
clobbers the vector registers, `FMOVD 8(RSP), F0`) and back to the passing stack check, to the
body at offset 24 with the frame of `BodyEntry 32`; `F0` (`V0`) holds `π` again, both at the
passing stack check (`MoreStep.vregs`) and at the body. -/
theorem objMoreF_witness :
    ¬ CheckPasses 32 16 s0m ∧ tailPlan spills.toList = .ok [⟨0, 8, 8, false, true⟩] ∧
      ∃ s' s1, MoreRel tab.check spills.toList s0m s' ∧ MStar msHookV code retM s0m s1 ∧
        BodyEntry 32 s0m s1 ∧ s1.pc = base + BitVec.ofNat 64 24 ∧ s'.v 0 = pi64 ∧
        s1.v 0 = pi64 := by
  obtain ⟨hc, haz, hchk, h0, hl, hsz, hret, htc, -, hpl⟩ := facts
  obtain ⟨s', s1, hmr, hrun, hbe, hpc, -, hv, -⟩ := obj_entry (H := msHookV) hc hl hsz hret
    machEntry_m (by rw [haz]; decide) (by decide)
    (fun ce tail gOff h n add htc' => by
      simp only [hchk, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [htc, Option.some.injEq, Prod.mk.injEq] at htc'
      obtain ⟨rfl, rfl⟩ := htc'
      rw [haz]
      exact msHookV_ok rfl rfl)
    (fun _ _ _ _ => tailSep)
  have hv0 : s'.v 0 = pi64 := by
    rcases hmr with rfl | ⟨ce, tail, gOff, sl, -, hpl', hst⟩
    · rfl
    · rw [hpl] at hpl'
      cases hpl'
      rcases hst.vregs 0 ⟨0, 8, 8, false, true⟩ (by decide) with e | e
      · exact e
      · rw [e]
        decide
  rw [haz] at hbe
  simp only [show (32 : Int) ≠ 0 by decide, ↓reduceIte] at hbe
  obtain ⟨-, hsp', -, h28', h29', h30'⟩ := hmr.keep
  rw [h0] at hpc
  refine ⟨by decide, hpl, s', s1, hmr, hrun,
    { sp := by rw [hbe.sp, hsp']; rfl
      lr := by rw [hbe.lr, h30']
      fp := by rw [hbe.fp, h29']
      r29 := hbe.r29
      g := by rw [hbe.g, h28'] }, hpc, hv0, by rw [hv, hv0]⟩

open GoFV.SSA.Sem in
/-- `fvalRel_vreloadVal` on `π` as a `float64` in a vector register whose upper half is junk:
the `D` reload clears it and keeps the relation. -/
theorem fvalRel_vreloadVal_witness :
    FValRel (.int .w64 0x400921fb54442d18)
      (vreloadVal 8 (0xdead0000000000000000000000000000 ||| pi64)) :=
  fvalRel_vreloadVal (by decide) (by unfold FValRel; decide) (by unfold ValFits; decide)

end GoFV.Proof.Witness.ObjMoreF
