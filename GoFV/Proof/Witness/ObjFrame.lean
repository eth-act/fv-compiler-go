import GoFV.Proof.Obj.Frame
import GoFV.Proof.Witness.GenG2
import GoFV.Asm.Flush
import GoFV.Asm.Parse

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: the prologue and the epilogue of `testInts` (`obj_entry`, `obj_exit`)

`test/makeslice/main/testInts,1.prog` of the corpus (`GenG2.testIntsProg`), run through the
assembler port and the validator as `obj-check` does (`GoFVTest/ObjCheck.lean`, `checkFile`):
`parseProgFile`, `flush`, the port's text, relocations and final Prog list as the `ObjIn`, and
`checkObj` on the `prog0` Progs and the function's spills. `testInts` is framed (`autosize = 32`,
it calls three functions) and has the small stack check (`MOVD 16(g), R16; CMP R16, RSP; BLS`):

```
 0 MOVD 16(R28), R16    12 MOVD.W R30, -32(RSP)   24 body …              48 MOVD -8(RSP), R29
 4 CMP R16, RSP         16 MOVD R29, -8(RSP)                             52 MOVD.P 32(RSP), R30
 8 BLS 60               20 SUB $8, RSP, R29                              56 RET
```

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`, as
`verifiedPipeline_witness`; `obj_facts`), `checkObj` accepts it with the frame size 32, a stack
check reading `16(g)`, the body at offset 24 and the `RET` (P0 index 14) at 48, not a leaf;
`linkCode` links it at `base = 0x10000` with every symbol at `0x100000`; the return address
`0x40` is outside the code; and the stack check passes from the entry state `s0` (`SP =
0x7fff0000`, `g = 0x9000` with a zero `stackguard0`, `R29 = SP − 8`, `LR = 0x40`). Then
`obj_entry` runs the prologue from `s0` to the body with the frame of `BodyEntry 32`
(`objFrame_entry_witness`) and `obj_exit` the epilogue from the body's state at the `RET` to the
saved `LR` with the frame popped (`objFrame_exit_witness`).
-/

namespace GoFV.Proof.Witness.ObjFrame

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj GoFV.Proof.Obj
open GoFV.SSA.Sem (MStar)

/-- The P0 Progs, the spills and the port's output of `testInts` (as `obj-check`). -/
def objIn : Except String (Array Prog × Array Spill × ObjIn) := do
  let pf ← parseProgFile GenG2.testIntsProg.toUTF8
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

/-- Whether an `Except` succeeded. -/
def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- The value of an `Except` that succeeded. -/
def getOk {ε α : Type} [Inhabited α] : Except ε α → α
  | .ok t => t
  | .error _ => default

theorem eq_getOk {ε α : Type} [Inhabited α] {e : Except ε α} (h : isOk e = true) :
    e = .ok (getOk e) := by
  cases e <;> simp_all [isOk, getOk]

/-- What `checkObj` returns on `testInts`. -/
def tab : Tab := getOk (checkObj ps spills obj)

def base : BitVec 64 := 0x10000

def sym : Nat → BitVec 64 := fun _ => 0x100000

/-- The caller's return address. -/
def retM : BitVec 64 := 0x40

/-- The linked code. -/
def code : Code := getOk (linkCode base sym obj.text obj.relocs.toList)

def sp0 : BitVec 64 := 0x7fff0000

/-- The entry: PC at `base`, `g = 0x9000`, `R29 = SP − 8`, `LR = retM`, the memory 0 (so
`stackguard0` is 0). -/
def s0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then sp0 - 8 else if k = 30 then retM else 0,
    sp := sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩, pc := base,
    mem := fun _ => 0 }

/-- The body's state at the `RET`'s epilogue (offset 48): `SP` lowered by the frame. -/
def t0 : MState := { s0 with sp := sp0 - 32, pc := base + 48 }

instance (az : Int) (gOff : Nat) (s : MState) : Decidable (CheckPasses az gOff s) := by
  unfold CheckPasses
  infer_instance

/-- What compiled evaluation checks: `checkObj` accepts `testInts` (frame 32, a stack check of
`16(g)`, body at 24, the `RET` at index 14 and offset 48, not a leaf), `linkCode` succeeds, the
text fits, `retM` has no code, and the stack check passes from `s0`. -/
def objFacts : Bool :=
  isOk (checkObj ps spills obj) && tab.autosize == 32 && tab.leaf == false &&
    tab.check.map (·.2.2) == some 16 && tab.offs[0]! == 24 && tab.offs[14]! == 48 &&
    isOk (linkCode base sym obj.text obj.relocs.toList) && decide (obj.text.size ≤ 2 ^ 64) &&
    code retM == none && decide (CheckPasses 32 16 s0) && decide (14 < ps.size) &&
    ps[14]?.map (fun p : Prog => p.as) == some .RET &&
    ps[14]?.map (fun p : Prog => p.to.type) == some .NONE &&
    ps[14]?.map (fun p : Prog => p.to.sym.isNone) == some true

theorem obj_facts : objFacts = true := by
  native_decide

/-- The facts of `obj_facts` as hypotheses. -/
theorem facts :
    checkObj ps spills obj = .ok tab ∧ tab.autosize = 32 ∧ tab.leaf = false ∧
      (∀ ce tail gOff, tab.check = some (ce, tail, gOff) → gOff = 16) ∧ tab.offs[0]! = 24 ∧
      tab.offs[14]! = 48 ∧ linkCode base sym obj.text obj.relocs.toList = .ok code ∧
      obj.text.size ≤ 2 ^ 64 ∧ code retM = none ∧ CheckPasses 32 16 s0 ∧
      ∃ hk : 14 < ps.size, ps[14].as = .RET ∧ ps[14].to.type = .NONE ∧ ps[14].to.sym = none := by
  have hf := obj_facts
  simp only [objFacts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, haz⟩, hleaf⟩, hchk⟩, h0⟩, h14⟩, hl⟩, hsz⟩, hret⟩, hpass⟩, hk⟩, has⟩,
    hty⟩, hsym⟩ := hf
  refine ⟨?_, haz, hleaf, fun ce tail gOff h => ?_, h0, h14, ?_, hsz, hret, hpass, hk, ?_, ?_, ?_⟩
  · exact eq_getOk hc
  · rw [h] at hchk
    simpa using hchk
  · exact eq_getOk hl
  · rw [Array.getElem?_eq_getElem hk] at has
    simpa using has
  · rw [Array.getElem?_eq_getElem hk] at hty
    simpa using hty
  · rw [Array.getElem?_eq_getElem hk] at hsym
    simpa using hsym

/-- `s0` is a call of `testInts` at `base` with 4096 bytes of stack below `SP`. -/
theorem machEntry : MachEntry code base 4096 s0 where
  pc := rfl
  spAlign := by decide
  room := by decide
  lrOutside := by
    obtain ⟨-, -, -, -, -, -, -, -, hret, -⟩ := facts
    exact hret
  gOutside := by decide
  fp := by decide

/-- **The prologue of `testInts`**: from the entry `s0`, the stack check (passing) and the frame
words run to the body at offset 24 in a state with the frame of `BodyEntry 32`. -/
theorem objFrame_entry_witness :
    ∃ s1, MStar Hooks.none code retM s0 s1 ∧ BodyEntry 32 s0 s1 ∧
      s1.pc = base + BitVec.ofNat 64 24 ∧
      (∀ k : Reg, k ≠ 16 → k ≠ 17 → k ≠ 20 → k ≠ 27 → k ≠ 29 → s1.x k = s0.x k) := by
  obtain ⟨hc, haz, -, hchk, h0, -, hl, hsz, hret, hpass, -⟩ := facts
  obtain ⟨s1, hrun, hbe, hpc, hx, -⟩ := obj_entry (H := Hooks.none) hc hl hsz hret machEntry
    (by rw [haz]; decide) (by decide) fun ce tail gOff h => by
      rw [hchk ce tail gOff h, haz]
      exact hpass
  rw [haz] at hbe
  rw [h0] at hpc
  exact ⟨s1, hrun, by simpa using hbe, hpc, hx⟩

/-- **The epilogue of `testInts`**: from the body's state `t0` at the `RET` (offset 48), the
words reload `R29` and `R30` from the frame, pop it and return to the saved `LR`. -/
theorem objFrame_exit_witness :
    ∃ t', MStar Hooks.none code retM t0 t' ∧ t'.pc = t0.word t0.sp ∧
      t'.x 30 = t0.word t0.sp ∧ t'.sp = t0.sp + 32 ∧ t'.x 29 = t0.word (t0.sp - 8) := by
  obtain ⟨hc, haz, hleaf, -, -, h14, hl, hsz, hret, -, hk, hr, hto, hsym⟩ := facts
  obtain ⟨t', hrun, hpc, hx30, hsp, hx29, -⟩ := obj_exit (H := Hooks.none) (t := t0) hc hl hsz
    hret hk hr hto hsym (by rw [h14]; rfl) (by decide)
  rw [haz, hleaf] at hpc hx30 hx29
  rw [haz] at hsp
  exact ⟨t', hrun, by simpa using hpc, by simpa using hx30, by simpa using hsp,
    by simpa using hx29⟩

end GoFV.Proof.Witness.ObjFrame
