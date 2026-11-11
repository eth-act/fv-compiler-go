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

/-- `s0` with a full stack: `stackguard0` all ones, so the stack check fails at the entry. -/
def s0m : MState :=
  { s0 with mem := fun a => if InWord (0x9000 + BitVec.ofNat 64 16) a then 0xff else 0 }

/-- What compiled evaluation checks: `checkObj` accepts `testInts` (frame 32, a stack check
ending at 12 with the morestack tail at 60 reading `16(g)`, body at 24, the `RET` at index 14 and
offset 48, not a leaf), `linkCode` succeeds, the text fits, `retM` has no code, the stack check
passes from `s0`, the tail calls symbol 9 (`runtime.morestack_noctxt`), which has no code, and
spills `R0` to `8(RSP)`. -/
def objFacts : Bool :=
  isOk (checkObj ps spills obj) && tab.autosize == 32 && tab.leaf == false &&
    tab.check == some (12, 60, 16) && tab.offs[0]! == 24 && tab.offs[14]! == 48 &&
    isOk (linkCode base sym obj.text obj.relocs.toList) && decide (obj.text.size ≤ 2 ^ 64) &&
    code retM == none && decide (CheckPasses 32 16 s0) && decide (14 < ps.size) &&
    ps[14]?.map (fun p : Prog => p.as) == some .RET &&
    ps[14]?.map (fun p : Prog => p.to.type) == some .NONE &&
    ps[14]?.map (fun p : Prog => p.to.sym.isNone) == some true &&
    tailCall obj.text obj.relocs.toList 60 == some (9, 0) &&
    code (sym 9 + BitVec.ofInt 64 0) == none && isOk (tailPlan spills.toList) &&
    getOk (tailPlan spills.toList) == [⟨0, 8, 8, false, false⟩]

theorem obj_facts : objFacts = true := by
  native_decide

/-- The facts of `obj_facts` as hypotheses. -/
theorem facts :
    checkObj ps spills obj = .ok tab ∧ tab.autosize = 32 ∧ tab.leaf = false ∧
      tab.check = some (12, 60, 16) ∧ tab.offs[0]! = 24 ∧
      tab.offs[14]! = 48 ∧ linkCode base sym obj.text obj.relocs.toList = .ok code ∧
      obj.text.size ≤ 2 ^ 64 ∧ code retM = none ∧ CheckPasses 32 16 s0 ∧
      (∃ hk : 14 < ps.size, ps[14].as = .RET ∧ ps[14].to.type = .NONE ∧ ps[14].to.sym = none) ∧
      tailCall obj.text obj.relocs.toList 60 = some (9, 0) ∧
      code (sym 9 + BitVec.ofInt 64 0) = none ∧
      tailPlan spills.toList = .ok [⟨0, 8, 8, false, false⟩] := by
  have hf := obj_facts
  simp only [objFacts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, haz⟩, hleaf⟩, hchk⟩, h0⟩, h14⟩, hl⟩, hsz⟩, hret⟩, hpass⟩, hk⟩, has⟩,
    hty⟩, hsym⟩, htc⟩, hcode⟩, hplok⟩, hpl⟩ := hf
  refine ⟨?_, haz, hleaf, hchk, h0, h14, ?_, hsz, hret, hpass, ⟨hk, ?_, ?_, ?_⟩, htc, hcode, ?_⟩
  · exact eq_getOk hc
  · exact eq_getOk hl
  · rw [Array.getElem?_eq_getElem hk] at has
    simpa using has
  · rw [Array.getElem?_eq_getElem hk] at hty
    simpa using hty
  · rw [Array.getElem?_eq_getElem hk] at hsym
    simpa using hsym
  · rw [eq_getOk hplok, hpl]

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

/-- So is `s0m`. -/
theorem machEntry_m : MachEntry code base 4096 s0m :=
  { machEntry with }

/-- A `runtime.morestack` for the witness: it returns to `X30` with `X30` set to `R3`, every other
register and the memory kept but `stackguard0` (`16(g)`), which it clears (the stack grown to its
bottom). -/
def msHook : Hooks := ⟨fun s => some (.ret
  { s with
    pc := s.x 30
    x := fun i => if i = 30 then s.x 3 else s.x i
    mem := fun a => if InWord (s.x 28 + BitVec.ofNat 64 16) a then 0 else s.mem a })⟩

/-- `msHook` meets the contract of `runtime.morestack` for `testInts` entered with `g = 0x9000`
and `SP = 0x7fff0000`. -/
theorem msHook_ok {s : MState} (hg : s.x 28 = 0x9000) (hsp : s.sp = sp0) :
    MorestackOK msHook code retM (sym 9 + BitVec.ofInt 64 0) 32 16 false s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcode, -⟩ := facts
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

/-- `testInts`' spill slot `8(RSP)` lies below `2^64` and apart from `g`. -/
theorem tailSep {s : MState} (hg : s.x 28 = 0x9000) (hsp : s.sp = sp0) : TailSep spills.toList s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hpl⟩ := facts
  intro sl h q hq
  rw [hpl] at h
  cases h
  simp only [List.mem_singleton] at hq
  subst hq
  rw [hg, hsp]
  decide

/-- The prologue of `testInts` from an entry `s` with `g = 0x9000` and `SP = 0x7fff0000`
(`obj_entry` under `msHook`): the state `s'` at the entry where the stack check passes, then the
body at offset 24 with the frame of `BodyEntry 32` over `s`. -/
theorem entry_of {s : MState} (hE : MachEntry code base 4096 s) (hg : s.x 28 = 0x9000)
    (hsp : s.sp = sp0) :
    ∃ s' s1, MoreRel false tab.check spills.toList s s' ∧ MStar msHook code retM s s1 ∧
      BodyEntry 32 s s1 ∧ s1.pc = base + BitVec.ofNat 64 24 ∧
      (∀ k : Reg, k ≠ 16 → k ≠ 17 → k ≠ 20 → k ≠ 27 → k ≠ 29 → s1.x k = s'.x k) := by
  obtain ⟨hc, haz, -, hchk, h0, -, hl, hsz, hret, -, -, htc, -⟩ := facts
  obtain ⟨s', s1, hmr, hrun, hbe, hpc, hx, -⟩ := obj_entry (H := msHook) hc hl hsz hret hE
    (by rw [haz]; decide) (by rw [hg]; decide)
    (fun ce tail gOff h n add htc' => by
      simp only [hchk, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [htc, Option.some.injEq, Prod.mk.injEq] at htc'
      obtain ⟨rfl, rfl⟩ := htc'
      rw [haz]
      exact msHook_ok hg hsp)
    (fun _ _ _ _ => tailSep hg hsp)
  rw [haz] at hbe
  simp only [show (32 : Int) ≠ 0 by decide, ↓reduceIte] at hbe
  obtain ⟨-, hsp', -, h28', h29', h30'⟩ := hmr.keep
  rw [h0] at hpc
  exact ⟨s', s1, hmr, hrun,
    { sp := by rw [hbe.sp, hsp']; rfl
      lr := by rw [hbe.lr, h30']
      fp := by rw [hbe.fp, h29']
      r29 := hbe.r29
      g := by rw [hbe.g, h28'] }, hpc, hx⟩

/-- **The prologue of `testInts`**: from the entry `s0`, whose stack check passes, to the body at
offset 24 with the frame of `BodyEntry 32`. -/
theorem objFrame_entry_witness :
    CheckPasses 32 16 s0 ∧ ∃ s' s1, MoreRel false tab.check spills.toList s0 s' ∧
      MStar msHook code retM s0 s1 ∧ BodyEntry 32 s0 s1 ∧ s1.pc = base + BitVec.ofNat 64 24 ∧
      (∀ k : Reg, k ≠ 16 → k ≠ 17 → k ≠ 20 → k ≠ 27 → k ≠ 29 → s1.x k = s'.x k) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hpass, -⟩ := facts
  exact ⟨hpass, entry_of machEntry rfl rfl⟩

/-- **The morestack path of `testInts`**: from the entry `s0m`, whose stack check fails
(`stackguard0` all ones), through the morestack tail (`msHook` clears the guard) and back to the
passing stack check, to the body at offset 24 with the frame of `BodyEntry 32`. -/
theorem objFrame_morestack_witness :
    ¬ CheckPasses 32 16 s0m ∧ ∃ s' s1, MoreRel false tab.check spills.toList s0m s' ∧
      MStar msHook code retM s0m s1 ∧ BodyEntry 32 s0m s1 ∧ s1.pc = base + BitVec.ofNat 64 24 ∧
      (∀ k : Reg, k ≠ 16 → k ≠ 17 → k ≠ 20 → k ≠ 27 → k ≠ 29 → s1.x k = s'.x k) :=
  ⟨by decide, entry_of machEntry_m rfl rfl⟩

/-- **The epilogue of `testInts`**: from the body's state `t0` at the `RET` (offset 48), the
words reload `R29` and `R30` from the frame, pop it and return to the saved `LR`. -/
theorem objFrame_exit_witness :
    ∃ t', MStar Hooks.none code retM t0 t' ∧ t'.pc = t0.word t0.sp ∧
      t'.x 30 = t0.word t0.sp ∧ t'.sp = t0.sp + 32 ∧ t'.x 29 = t0.word (t0.sp - 8) := by
  obtain ⟨hc, haz, hleaf, -, -, h14, hl, hsz, hret, -, ⟨hk, hr, hto, hsym⟩, -⟩ := facts
  obtain ⟨t', hrun, hpc, hx30, hsp, hx29, -⟩ := obj_exit (H := Hooks.none) (t := t0) hc hl hsz
    hret hk hr hto hsym (by rw [h14]; rfl) (by decide)
  rw [haz, hleaf] at hpc hx30 hx29
  rw [haz] at hsp
  exact ⟨t', hrun, by simpa using hpc, by simpa using hx30, by simpa using hsp,
    by simpa using hx29⟩

end GoFV.Proof.Witness.ObjFrame
