import GoFV.Proof.Obj.Sim
import GoFV.Proof.Witness.ObjFrame
import GoFV.Asm.ConstLoad

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: `SBFIZ` in `checkObj` (#553)

`checkObj` models `SBFIZ $lsb, Rn, $width, Rd` (and `SBFIZW`) as `SBFM Rd, Rn, #(-lsb mod w),
#(width - 1)` (`Ex.mkBfm sf 0`; `sbfiz_bfm`: P0's `sbfiz`, the field sign-extended and shifted
left, is that bitfield move).

`objSbfiz_witness`: `std/std/runtime/(*stkframe).argBytes,1.prog` of the corpus
(`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim as `fProg`), run through the
assembler port and the validator as `obj-check` does (`GoFVTest/ObjCheck.lean`, `checkFile`:
`parseProgFile`, `flush`, P0' by `p0Prime`, `checkObj` on P0', the spills and the port's output).
By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`, as
`ObjBarrier.barrier_facts`; `sbfiz_facts`), `checkObj` accepts it (it rejected it before, `opcode
not modelled: SBFIZ`); its Prog `SBFIZ $3, R0, $32, R0` falls through, its word decodes to
`SBFM X0, X0, #61, #31`, and `progStep` runs it from `s0` (`R0 = 0x80000001`, a negative 32-bit
field) to `R0 = 0xfffffffc00000008`, the field sign-extended and shifted by 3. `progSym_sound` on
that Prog relates the step to the Prog's symbolic effect (`HoldsCore`).
-/

namespace GoFV.Proof.Witness.ObjSbfiz

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj GoFV.Proof.Obj
open GoFV.Proof.Witness.ObjFrame (isOk getOk eq_getOk)

/-- `std/std/runtime/(*stkframe).argBytes,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "(*stkframe).argBytes" 1
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
type t1 8 8 8 1 01 "*stkframe"
name n1 "frame" PPARAM t1 1 "runtime.frame" 0 a3
type t2 8 8 0 0 - "uintptr"
name n2 "~r0" PPARAMOUT t2 1 "runtime.~r0" 0 a4
type t3 16 8 16 1 02 "bitvector"
name n3 "argMap" PAUTO t3 1 "runtime.argMap" 0 a7
name n4 ".autotmp_3" PAUTO t3 1 "runtime..autotmp_3" 0 -
type t4 1 1 0 0 - "bool"
name n5 ".autotmp_4" PAUTO t4 1 "runtime..autotmp_4" 0 -
name n6 ".autotmp_5" PAUTO t3 3 "runtime..autotmp_5" 0 -
name n7 ".autotmp_6" PAUTO t4 3 "runtime..autotmp_6" 0 -
type t5 4 4 0 0 - "int32"
name n8 "argMapn" PAUTO t5 3 "runtime.argMapn" 0 a8
type t6 8 8 8 1 01 "*uint8"
name n9 "argMapbytedata" PAUTO t6 3 "runtime.argMapbytedata" 0 a9
in n1 0 used
in n2 0 outregs
in n3 0 used
in n4 0 used,autotmp
in n5 0 used,autotmp
in n6 0 used,autotmp
in n7 0 used,autotmp
in n8 0 used
in n9 0 used
out n1 0 used
opt n4 0 autotmp
opt n6 0 autotmp
opt n3 0 -
opt n9 0 -
opt n2 0 outregs
opt n8 0 -
opt n5 0 autotmp
opt n7 0 autotmp
stack 0 0 8
end
genin
posbase p129 "runtime/stkframe.go" 1 1 -1 126 "runtime/stkframe.go" "runtime/stkframe.go" 1 1
sym y1 "runtime.(*stkframe).argBytes" 1
curfn p129:72:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 72 200080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.(*stkframe).argBytes.arginfo1" 0
sym y5 "runtime.(*stkframe).argBytes.argliveinfo" 0
sym y6 "runtime.(*stkframe).argMapInternal" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p129:72:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p129:72:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p129:72:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p129:72:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p129:72:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p129:72:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p129:73:13:1:0
p 7 7 0 0 0 - MOVD 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p129:73:13:1:0
p 8 8 0 0 0 - MOVW 0 MEM/8193/0/0/NONE/0/8/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p129:73:13:2:0
p 9 9 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/-2147483648/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p129:73:19:2:0
p 10 10 0 0 0 - CMPW 0 REG/8194/0/0/NONE/0/0/-/- 8193 - _ 0 0 p129:73:19:2:0
p 11 11 0 0 0 - BEQ 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@14 0 0 p129:73:25:2:0
p 12 12 0 0 0 - MOVD 0 REG/8193/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p129:74:26:1:0
p 13 13 0 0 0 - RET 0 _ 0 - _ 0 0 p129:74:23:2:0
p 14 14 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p129:78:35:1:0
p 15 15 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p129:78:35:1:0
p 16 16 0 0 0 - SBFIZ 0 CONST/0/0/0/NONE/0/3/-/- 8192 0:CONST/0/0/0/NONE/0/32/-/- REG/8192/0/0/NONE/0/0/-/- 0 0 p129:79:27:1:0
p 17 17 0 0 0 - RET 0 _ 0 - _ 0 0 p129:79:35:2:0
p 18 18 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 72 200080
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
dbgloc 0 1:-10000:3:26:50
dbgregout n2
dbgpc 3:26:13
end
asm
sym y7 "runtime.morestack_noctxt" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i8 0 0 p129:72:6:0:0
p 19 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p129:72:6:0:0
p 20 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p129:72:6:0:0
p 21 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p129:72:6:0:0
p 22 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@33 0 0 p129:72:6:0:0
p 23 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p129:72:6:0:0
p 24 12 32 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-32/-/- 0 0 p129:72:6:0:1
p 25 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p129:72:6:0:0
p 26 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p129:72:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p129:72:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p129:72:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p129:72:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p129:72:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p129:72:6:2:0
p 6 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p129:73:13:1:0
p 7 24 0 0 333 - MOVD 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p129:73:13:1:0
p 8 28 0 0 392 - MOVW 0 MEM/8193/0/0/NONE/87/8/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p129:73:13:2:0
p 9 32 0 0 319 - MOVD 0 CONST/0/0/0/NONE/24/-2147483648/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p129:73:19:2:0
p 10 36 0 0 92 - CMPW 0 REG/8194/0/0/NONE/2/0/-/- 8193 - NONE/0/0/0/NONE/1/0/-/- 0 0 p129:73:19:2:0
p 11 40 0 0 80 - BEQ 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/14/-/@14 0 0 p129:73:25:2:0
p 12 44 0 0 301 - MOVD 0 REG/8193/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p129:74:26:1:0
p 13 48 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p129:74:23:2:0
p 27 52 -32 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/32/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p129:74:23:2:0
p 28 56 32 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p129:74:23:2:0
p 14 60 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p129:78:35:1:0
p 15 60 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y6/- 0 0 p129:78:35:1:0
p 16 64 0 0 81 - SBFIZ 0 CONST/0/0/0/NONE/17/3/-/- 8192 0:CONST/0/0/0/NONE/17/32/-/- REG/8192/0/0/NONE/2/0/-/- 0 0 p129:79:27:1:0
p 17 68 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p129:79:35:2:0
p 29 72 -32 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/32/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p129:79:35:2:0
p 30 76 32 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p129:79:35:2:0
p 31 80 -32 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p129:79:35:2:0
p 32 80 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p129:72:6:0:0
p 33 80 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p129:72:6:0:0
p 34 80 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p129:72:6:0:0
p 35 84 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p129:72:6:0:0
p 36 88 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y7/- 0 0 p129:72:6:0:0
p 37 92 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p129:72:6:0:0
p 38 92 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p129:72:6:0:0
p 39 96 32 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@19 0 0 p129:72:6:0:0
fn y1 8 24 0 0 72 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 112 0 900b40f9ff6330eb49020054fe0f1ef8fd831ff8fd2300d1010040f9210880b9e28361b23f00026ba0000054e00301aafd835ff8fe0742f8c0035fd600000094007c7d93fd835ff8fe0742f8c0035fd6e00700f9e3031eaa00000094e00740f9e8ffff17000000000000000000000000 2
reloc 60 4 R_CALLARM64 0 y6
reloc 88 4 R_CALLARM64 0 y7
pcln y12 y13 y14 y15 y8,y9,y10,y11 y2,y3,_,_,_,y4,y5
usedfiles 126
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y8 SRODATA 11 1 28000 0001010202030111020500 0
data y9 SRODATA 7 1 28000 000f0405030800 0
data y10 SRODATA 0 1 28000 - 0
data y11 SRODATA 5 1 28000 0006041600 0
data y12 SRODATA 11 1 28000 0204400a3f0140043f0900 0
data y13 SRODATA 4 1 28000 fe011c00 0
data y14 SRODATA 14 1 28000 92010602050204080102040d0800 0
data y15 SRODATA 3 1 28000 001c00 0
end
dwarf
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
sym y20 "go:info.*runtime.stkframe" 0
sym y21 "go:info.uintptr" 0
sym y22 "type:uintptr" 0
dwfn y16 y17 y18 - y19 "runtime.(*stkframe).argBytes" 126:72 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime.stkframe" 0 0 1 p129:72:7:0:0
dwname n4 1 0 1 0 0 0 0 0 - - "runtime.bitvector" 0 0 1 p129:78:12:0:0
dwname n6 1 0 1 0 0 0 0 0 - - "runtime.bitvector" 0 0 1 p129:78:12:0:0
dwname n3 1 0 0 0 0 0 0 0 - - "runtime.bitvector" 0 0 1 p129:78:2:0:0
dwname n9 1 0 0 0 0 0 0 0 - - "*uint8" 0 0 1 p129:78:2:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uintptr" 0 0 1 p129:72:35:0:0
dwname n8 1 0 0 0 0 0 0 0 - - "int32" 0 0 1 p129:78:2:0:0
dwname n5 1 0 1 0 0 0 0 0 - - "bool" 0 0 1 p129:78:12:0:0
dwname n7 1 0 1 0 0 0 0 0 - - "bool" 0 0 1 p129:78:12:0:0
var 0 0 "frame" 5 1 0 0 0 8 y20 "runtime/stkframe.go" 72 7 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y21 "runtime/stkframe.go" 72 35 0 1 0 0 -
scope 0 0 - 0,1
data y16 SDWARFFCN 71 0 0 0372756e74696d652e282a73746b6672616d65292e617267427974657300000070019c7f00000048012d6672616d6500004800000000000000002e7e7230000148000000000000 5
reloc 0 0 R_USETYPE 0 y22
reloc 30 2 R_DWTXTADDR_U2 0 y1
reloc 50 4 R_DWARFSECREF 0 y20
reloc 54 4 R_DWARFSECREF 0 y17
reloc 65 4 R_DWARFSECREF 0 y21
data y17 SDWARFLOC 9 0 0 010000040030015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y18 SDWARFRANGE 0 0 0 - 0
data y19 SDWARFLINES 40 0 0 0009020000000000000000047f03c200140a8788063706b00637068b38063706037d830220000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- P0' (`p0Prime`), the spills and the port's output of `runtime.(*stkframe).argBytes` (as
`obj-check`). -/
def objIn : Except String (Array Prog × Array Spill × ObjIn) := do
  let pf ← parseProgFile fProg.toUTF8
  let out ← flush pf
  let ps ← p0Prime (fun n => out.st.symIdx[(GoFV.SSA.GoStr.ofString n, Obj.ABI0.toNat)]?)
    pf.prog0.progs
  return (ps, pf.prog0.fn.spills,
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

/-- What `checkObj` returns on `runtime.(*stkframe).argBytes`. -/
def tab : Tab := getOk (checkObj ps spills obj)

/-- The index of the `SBFIZ` among the Progs. -/
def jS : Nat := (ps.findIdx? (·.as == .SBFIZ)).getD 0

/-- `SBFIZ $3, R0, $32, R0`. -/
def pS : Prog := ps[jS]!

/-- The ID layout of the Progs with the frame `az`, `ez`. -/
def L (az ez : Int) : Link := Link.byId (fun _ => 0x100000) 0x10000 az ez ps.toList

/-- A state with `R0 = 0x80000001` (bit 31 set: the 32-bit field is negative), every other
register `0`. -/
def s0 : MState :=
  { x := fun r => if r = 0 then 0x80000001 else 0, sp := 0x8000, v := fun _ => 0,
    nzcv := ⟨false, false, false, false⟩, pc := 0x1000, mem := fun _ => 0 }

/-- `R0` after `progStep L p s`. -/
def r0Of (L : Link) (p : Prog) (s : MState) : Option (BitVec 64) :=
  match progStep L p s with
  | .ok s' => some (s'.x 0)
  | .error _ => none

theorem r0Of_some {L : Link} {p : Prog} {s : MState} {r : BitVec 64} (h : r0Of L p s = some r) :
    ∃ s', progStep L p s = .ok s' ∧ s'.x 0 = r := by
  unfold r0Of at h
  split at h
  · next s' hst => exact ⟨s', hst, Option.some.inj h⟩
  · cases h

/-- `R0` after `progStep` of `pS` from `s0`. -/
def r0After (az ez : Int) : Option (BitVec 64) := r0Of (L az ez) pS s0

/-- What compiled evaluation checks: `checkObj` accepts the function; its Prog `pS` is
`SBFIZ`, no skip, falls through (`progSym`); its word decodes to `SBFM X0, X0, #61, #31`; and
`progStep` of it from `s0` gives `R0 = 0xfffffffc00000008`. -/
def sbfizFacts : Bool :=
  isOk (checkObj ps spills obj) && pS.as == .SBFIZ && !pS.isSkip &&
    isOk (progSym tab.autosize tab.extrasize pS) &&
    (getOk (progSym tab.autosize tab.extrasize pS)).2 == .fall &&
    decode (wordAt obj.text tab.offs[jS]!) == some (.bitfield true 0 61 31 0 0) &&
    r0After tab.autosize tab.extrasize == some 0xfffffffc00000008

theorem sbfiz_facts : sbfizFacts = true := by
  native_decide

/-- `progSym_sound` on `pS` in the layout `L az ez`, from `s0`. -/
private theorem sbfiz_step {az ez : Int} {σ : Sym} (hps : progSym az ez pS = .ok (σ, .fall))
    (hsk : pS.isSkip = false) (hr : r0After az ez = some 0xfffffffc00000008) :
    ∃ s', progStep (L az ez) pS s0 = .ok s' ∧ s'.x 0 = 0xfffffffc00000008 ∧
      HoldsCore ⟨s0, (L az ez).sym⟩ σ s' := by
  have hL1 : (L az ez).autosize = az := rfl
  have hL2 : (L az ez).extrasize = ez := rfl
  obtain ⟨s', hst, hx⟩ := r0Of_some hr
  exact ⟨s', hst, hx, (progSym_sound hps hL1 hL2 hsk hst).2.1⟩

/-- **`checkObj` on a function with `SBFIZ`**: it accepts `runtime.(*stkframe).argBytes`, whose
`SBFIZ $3, R0, $32, R0` assembles to `SBFM X0, X0, #61, #31`; from `R0 = 0x80000001` the Prog
gives `R0 = 0xfffffffc00000008` (the 32-bit field sign-extended, shifted by 3), and
`progSym_sound` relates that step to the Prog's symbolic effect, which `checkObj` compared with
the word's. -/
theorem objSbfiz_witness :
    checkObj ps spills obj = .ok tab ∧ pS.as = .SBFIZ ∧
      decode (wordAt obj.text tab.offs[jS]!) = some (.bitfield true 0 61 31 0 0) ∧
      ∃ σ s', progSym tab.autosize tab.extrasize pS = .ok (σ, .fall) ∧
        progStep (L tab.autosize tab.extrasize) pS s0 = .ok s' ∧ s'.x 0 = 0xfffffffc00000008 ∧
        HoldsCore ⟨s0, (L tab.autosize tab.extrasize).sym⟩ σ s' := by
  have hf := sbfiz_facts
  simp only [sbfizFacts, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hf
  obtain ⟨⟨⟨⟨⟨⟨hc, has⟩, hsk⟩, hpo⟩, hpe⟩, hd⟩, hr⟩ := hf
  have hps := eq_getOk hpo
  generalize getOk (progSym tab.autosize tab.extrasize pS) = g at hps hpe
  obtain ⟨σ, pc⟩ := g
  simp only at hpe
  subst hpe
  obtain ⟨s', hst, hx, hH⟩ := sbfiz_step hps hsk hr
  exact ⟨eq_getOk hc, has, hd, σ, s', hps, hst, hx, hH⟩

end GoFV.Proof.Witness.ObjSbfiz
