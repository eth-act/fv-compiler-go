import GoFV.Proof.Obj.EndToEnd
import GoFV.Proof.Witness.ObjEndToEndAtSP
import GoFV.Proof.Witness.GenG11

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: generic SSA to machine words in a closure (`verified_mach`)

`adder.func1` of `examples/closures/main` (`GenG11`: `adder.func1,1.ssa` and `.prog` of
quick-v10), the closure `func(x int) int { return x + k }` of `adder`, which reads its captured
`k` off the closure context:

```go
func adder(k int) func(int) int {
	return func(x int) int { return x + k }
}
```

Its generic SSA input (the export's first section, in the pass environment `gofv-ssa-opt
--verified` builds, `ObjEndToEnd.baseEnv`) goes through `verifiedPipelineFull` (`fullyVerified`)
to the allocated function, whose entry block `b1` is `v7 = LoweredGetClosurePtr` (`R26`),
`v6 = ArgIntReg` (`R0`), `v1 = InitMem`, then `v9 = MOVDload [8] v7` (`R1`), `v11 = ADD v6 v9`
(`R0`), `v12 = MakeResult`, `Ret`; genssa's Progs `MOVD 8(R26), R1; ADD R1, R0, R0; RET` (a
frameless leaf without a stack check: `ObjG7.envFacts`, `otab.check = none`). `verified_mach`
applies with every premise discharged and the closure context present:

* the environment `env` is the Phase 1 test environment `plRunEnv` with the closure context
  `cloH`, a pointer to the funcval `heap 1`, which the input memory `mem` holds: its code word
  (the fragments of a pointer to the symbol `main.adder.func1`) and the captured `k = 5`; its
  `VPre` facts hold (`initAvoidsC`: the closure conjunct of `InitAvoids`; `wbPreC`), `ArgPtrsOK`
  with the context's `¬ NilBase` (`cloH_nilBase`), `NoNilFault` by `sameRun` (the scheduled
  function loads off the closure pointer, so it is no `noAct` one). On `x = 7` the generic `run`
  reads `k` through `GetClosurePtr`, `OffPtr [8]` and `Load` and returns `12`;
* the run's first state `sI` is after the three entry values (`entryLen`, which counts
  `LoweredGetClosurePtr`, is 3): `R0 = 7`, `R26 = cloA`, the closure object's address `2^41`
  (`Addrs.fixed`), and the frame memory `memI`. The machine enters at `ObjG7.base` with
  `X0 = 7`, `X26 = cloA` (`EntryMatch.regs` relates `R26` to the closure context: the ABIInternal
  caller's obligation) and the object's bytes at `cloA` (`memInj`: the code word `GenG2.symA`,
  where every symbol is linked, and `5`);
* `RunPre` from `(b1, 3)`: the load `v9` at `sI`, the only state the run reaches there
  (`lreach_at_start`), reads 8 valid bytes of the closure object (`loadOK`, G3's premise in
  `G54Pre`), every later value is a simple op (`simpleFrom`), and the trusted `CloOK` holds at every
  reached state by `cloOK_of_cloBefore` (`cloBefore lc 3`: the only `LoweredGetClosurePtr` runs
  before the start).

`verified_mach` then gives the `runLoc` refinement and a `runMach` of the linked words that
returns to the caller's `0x40` (`MachRet`) with the result `12 = 7 + 5` in `X0` (`ResultRel`).
By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `obj_facts`,
`e2e_facts`): the export parses, the pipeline is `fullyVerified`, the validators accept, the runs
return `12`, and the states and tables are as stated.
-/

namespace GoFV.Proof.Witness.ObjEndToEndClo

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Verified GoFV.Gen.Check GoFV.Arm64 GoFV.Asm
open GoFV.Asm.CheckObj
open GoFV.Proof.Gen GoFV.Proof.Obj GoFV.Proof.Pipeline GoFV.Proof.PipelineFull
open GoFV.Proof (OutcomeRefines enterListLoc)
open GoFV.Proof.Witness (plRunEnv plRunEnv_mono plRunEnv_frameSafe plRunEnv_allocNonNil
  plRunEnv_wbPre plRunEnv_tempOblivious plRunEnv_memOps plRunEnv_keeps plRunEnv_allocZero
  plRunEnv_growLen plRunEnv_ifaceEq noArgPtrB noNilPtrB)
open GoFV.Proof.Witness.ObjFrame (isOk getOk eq_getOk)
open GoFV.Proof.Witness.ObjEndToEnd (baseEnv padTables)
open GoFV.Proof.Witness.ObjWhole (isPoison pAddr ι addrAgree noWbICall noMemEq
  noWbICall_spec noMemEq_spec)
open GoFV.Proof.Witness.ObjEndToEndAtSP (isOOF isOOF_spec simpleFrom_blk)

/-! ## The generic input -/

/-- The parsed export of `adder.func1`. -/
def exIn : Except String (ExportFile × ExportExt) := parseExportExt GenG11.fSsa.toUTF8

def file : ExportFile :=
  match exIn with
  | .ok x => x.1
  | .error _ => default

def ext : ExportExt :=
  match exIn with
  | .ok x => x.2
  | .error _ => default

/-- The first section: the input of `number lines`. -/
def sec0 : Section := (file.sections[0]?).getD default

def penv : PassEnv := baseEnv file (padTables (({} : Tables).addAll sec0.defs) file.frontendTables)

/-- The generic SSA input. -/
def f0 : Func := sec0.func

def dcl : Nat := (ext.dclLen? 0).getD 0

/-! ## The closure -/

/-- The machine address of the closure object `heap 1` (its Phase 1 address, `Addrs.fixed`). -/
def cloA : BitVec 64 := 0x20000000000

/-- The closure context: a pointer to the funcval `heap 1`. -/
def cloH : Val := .ptr ⟨.heap 1, 0⟩

/-- `plRunEnv` inside the closure: the top-level closure context `cloH`. -/
def env : Env := { plRunEnv with closure := some cloH }

/-- The funcval's code pointer: the symbol `main.adder.func1`. -/
def codeP : Ptr := ⟨.global "main.adder.func1", 0⟩

/-- The funcval: the code pointer and the captured `k = 5`. -/
def cloAlloc : Alloc :=
  { data := #[.frag codeP 0, .frag codeP 1, .frag codeP 2, .frag codeP 3, .frag codeP 4,
      .frag codeP 5, .frag codeP 6, .frag codeP 7, .b 5, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] }

/-- The input memory: the funcval. -/
def mem : Mem := { blocks := #[(.heap 1, cloAlloc)], nextHeap := 2 }

/-- The argument `x = 7`. -/
def args : List Val := [.i64 7]

/-! ## The Progs and the assembled words -/

abbrev ps : Array Prog := GenG11.ps
abbrev bs : ID → Option Nat := GenG11.bs
abbrev g : G2In := GenG11.g
abbrev tab : PcTab := GenG11.tab

def objIn : Except String (Array Spill × ObjIn) := ObjG7.objOf GenG11.fProg

def spills : Array Spill :=
  match objIn with
  | .ok x => x.1
  | .error _ => #[]

def obj : ObjIn :=
  match objIn with
  | .ok x => x.2
  | .error _ => ⟨ByteArray.empty, #[], #[]⟩

/-- What `checkObj` returns. -/
def otab : Tab := getOk (checkObj ps spills obj)

/-- The linked code. -/
def code : Code := getOk (linkCode ObjG7.base (fun _ => GenG2.symA) obj.text obj.relocs.toList)

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, no frame, every symbol at `symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 0 0 ps.toList

/-! ## The activation -/

/-- The activation of `runLoc`'s context `lc`: frameless, `SP = 0x7fff0000`, `g = 0x9000`,
`LR = 0x40`, `FP = SP - 8`, the blocks at `ObjWhole.ι` (the heap at its Phase 1 addresses). -/
def E0 (lc : LocCtx) : MatchEnv :=
  { lc, ι, sp := 0x7fff0000, slot := fun _ => none, g := 0x9000, lr := 0x40,
    fp := 0x7fff0000 - 8, framed := false, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The machine memory: `x`'s image (7) at its address, the funcval at `cloA` (the code word
`GenG2.symA`, whose byte 5 is 1, and `5`). -/
def mmI : Memory := fun a =>
  if a = pAddr then 7 else if a = cloA + 5 then 1 else if a = cloA + 8 then 5 else 0

/-- The machine at the function's entry: `X0 = 7`, the closure context `X26 = cloA`. -/
def s0 : MState :=
  { x := fun k => if k = 0 then 7 else if k = 26 then cloA else if k = 28 then 0x9000
      else if k = 29 then 0x7fff0000 - 8 else if k = 30 then 0x40 else 0,
    sp := 0x7fff0000, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩, pc := ObjG7.base,
    mem := mmI }

/-- The frame memory of `runLoc`'s first state: the funcval, `plRunEnv`'s globals, the
outgoing-arguments area, `x`'s image, the result slot and `k`'s home (a frame temporary). -/
def memI : Mem :=
  { blocks := #[(.heap 1, cloAlloc),
      (.global "main.g", { data := #[.b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] }),
      (.global "runtime.writeBarrier", { data := #[.b 0, .b 0, .b 0, .b 0], writable := false }),
      (.outargs 0, { data := #[] }),
      (.local 0 3, { data := #[.b 7, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] }),
      (.local 0 4, { data := #[.poison, .poison, .poison, .poison, .poison, .poison, .poison,
        .poison] }),
      (.temp 0 5, { data := #[.poison, .poison, .poison, .poison, .poison, .poison, .poison,
        .poison] })],
    nextHeap := 2 }

/-! ## Checks -/

/-- Block `b1` of `lc`. -/
def blkOf (lc : LocCtx) : Block := (lc.ctx.f.block? 1).getD default

/-- The load `v9` of `lc`. -/
def v9Of (lc : LocCtx) : Value := (lc.ctx.f.value? 9).getD default

/-- The tables `checkG64L` gives on `lc`. -/
def ktOf (lc : LocCtx) : KTab := (getOk (checkG64L lc ps bs g)).2

/-- The value is the 64-bit integer `x`. -/
def isW64 (x : BitVec 64) : Val → Bool
  | .int .w64 y => y == x
  | _ => false

theorem isW64_spec {x : BitVec 64} {v : Val} (h : isW64 x v = true) : v = .int .w64 x := by
  unfold isW64 at h
  split at h
  · simp only [beq_iff_eq] at h
    subst h
    rfl
  · cases h

/-- `R0` holds `x = 7`, `R26` (register 25) the closure context's word `cloA`, every other
register `poison`; no flags, no slot, the frame memory. -/
def sIIs (s : LocState) : Bool :=
  (List.range s.regs.size).all (fun r =>
      match s.regs[r]? with
      | some v => if r = 0 then isW64 7 v else if r = 25 then isW64 cloA v else isPoison v
      | none => true) &&
    isPoison s.flags && s.slots.isEmpty &&
    match s.mem with
    | .mem m => decide (m = memI)
    | _ => false

theorem sIIs_spec {s : LocState} (h : sIIs s = true) :
    (∀ r v, s.regs[r]? = some v → (r = 0 → v = .int .w64 7) ∧ (r = 25 → v = .int .w64 cloA) ∧
      (r ≠ 0 → r ≠ 25 → v = .poison)) ∧
      s.flags = .poison ∧ s.slots = [] ∧ s.mem = .mem memI := by
  simp only [sIIs, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.isEmpty_iff] at h
  obtain ⟨⟨⟨hr, hf⟩, hs⟩, hm⟩ := h
  refine ⟨fun r v hv => ?_, ?_, hs, ?_⟩
  · have hlt := (Array.getElem?_eq_some_iff.1 hv).1
    have := hr r hlt
    rw [hv] at this
    dsimp only at this
    refine ⟨fun h0 => ?_, fun h25 => ?_, fun h0 h25 => ?_⟩
    · subst h0
      simp only [↓reduceIte] at this
      exact isW64_spec this
    · subst h25
      simp only [show (25 : Nat) ≠ 0 by decide, ↓reduceIte] at this
      exact isW64_spec this
    · simp only [h0, h25, ↓reduceIte] at this
      unfold isPoison at this
      split at this
      · rfl
      · cases this
  · unfold isPoison at hf
    split at hf
    · assumption
    · cases hf
  · split at hm
    · simp only [decide_eq_true_eq] at hm
      subst hm
      assumption
    · cases hm

def isBoolTy : Ty → Bool
  | .bool => true
  | _ => false

/-- G3's load premise at `s`, checked: the load reads its bytes at its address, and loads no
boolean. -/
def loadOK (lc : LocCtx) (s : LocState) (v : Value) : Bool :=
  match loadOp? v.op, v.args[0]? with
  | some (_, n, _), some a =>
    match s.read lc a with
    | .ok x =>
      match symAddr lc.ctx v x, s.mem with
      | some p, .mem m => (m.read p n).isSome && !isBoolTy (lc.ty v.id)
      | _, _ => false
    | _ => true
  | _, _ => true

theorem loadOK_spec {lc : LocCtx} {s : LocState} {v : Value} (h : loadOK lc s v = true) :
    ∀ as n sg, loadOp? v.op = some (as, n, sg) → ∀ a x, v.args[0]? = some a →
      s.read lc a = .ok x → ∃ p mm bs, symAddr lc.ctx v x = some p ∧ s.mem = .mem mm ∧
        mm.read p n = some bs ∧
        (lc.ty v.id = .bool → ∀ y, mm.load (.int .w8) p = .int .w8 y → y.toNat < 2) := by
  intro as n sg hl a x ha hx
  unfold loadOK at h
  rw [hl, ha] at h
  simp only [hx] at h
  split at h
  · rename_i p m hp hm
    simp only [Bool.and_eq_true, Option.isSome_iff_exists, Bool.not_eq_true'] at h
    obtain ⟨⟨bs, hbs⟩, hb⟩ := h
    exact ⟨p, m, bs, hp, hm, hbs, fun ht => by rw [ht] at hb; cases hb⟩
  · cases h

/-- The outcome returns the 64-bit integer `12`. -/
def isRet12 : Outcome → Bool
  | .returned [.int .w64 x] _ => x == 12
  | _ => false

theorem isRet12_spec {o : Outcome} (h : isRet12 o = true) :
    ∃ mm, o = .returned [.int .w64 12] mm := by
  unfold isRet12 at h
  split at h
  · simp only [beq_iff_eq] at h
    subst h
    exact ⟨_, rfl⟩
  · cases h

/-- No symbol of `adder.func1` is one of `plRunEnv`'s globals. -/
def symsOut : Bool :=
  g.syms.all fun x =>
    x.1.toStringLossy != "main.g" && x.1.toStringLossy != "runtime.writeBarrier"

/-- What compiled evaluation checks of the machine side: `checkObj` accepts with no frame and no
stack check, the linked code, no `CALL (Rn)`, the return address `0x40` is no P0 address nor
`endP`, the P0 address of the entry's value 3 maps to the body's start, `memI`'s keys are
distinct. -/
def objFacts : Bool :=
  ObjG7.envFacts ps spills obj && otab.check.isNone &&
    ps.toList.all (fun p => addrP GenG2.text p.id != 0x40) &&
    (0x40 : BitVec 64) != endP GenG2.text ps.toList &&
    ObjEnv.map otab ps L ObjG7.base (pcOfTab GenG2.text ps.toList tab 1 3) ==
      ObjG7.base + BitVec.ofNat 64 (otab.offs[0]!) &&
    decide ((memI.blocks.toList.map (·.1)).Nodup) && symsOut && ObjG7.noICall ps

theorem obj_facts : objFacts = true := by
  native_decide

/-- What compiled evaluation checks of a `runLoc` context `lc`: `checkG64L` accepts genssa's
Progs of `adder.func1` against it with `tab`, `retRegsOK` its return (the result in `R0`); no
frame variable accessed, no home slot, static or indirect call, write barrier or
`LoweredMemEq`; the entry is `b1`, with six values, the fourth the load `v9`; the first three run
from `runLoc`'s first state on `x = 7` in `env` to `R0 = 7`, `R26 = cloA` and the frame memory,
where `v9`'s load reads valid bytes (`loadOK`); `R0` and `R26` have class 64 after them, no
upper-bit fact is carried (`uL35`); simple ops after `v9` (`simpleFrom`); `entryStoresOK`,
`argsOK` (no `Arg`), `cloBefore` (the only `LoweredGetClosurePtr` before the start); `memTyL`, no
float constant symbol, and it does not need G48's mode (`needs48`). -/
def lcFacts (lc : LocCtx) : Bool :=
  isOk (checkG64L lc ps bs g) && (getOk (checkG64L lc ps bs g)).1 == tab &&
    retRegsOK lc (ktOf lc) && ownOutRegs lc == [0] &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty && GenG2.noCalls lc && noWbICall lc &&
    noMemEq lc && lc.ctx.f.entry == 1 && lc.ctx.f.blocks.toList.contains 1 &&
    (lc.ctx.f.block? 1).isSome && (blkOf lc).values.size == 6 &&
    (blkOf lc).values[3]? == some 9 && (lc.ctx.f.value? 9).isSome &&
    (v9Of lc).op == .ARM64MOVDload &&
    GenG1.okThen (enterListLoc env lc (locInit env lc args mem) ((blkOf lc).values.toList.take 3))
      (fun sI => sIIs sI && loadOK lc sI (v9Of lc)) &&
    (kAt lc (ktOf lc) 1 (blkOf lc) 3).get 0 == some 64 &&
    (kAt lc (ktOf lc) 1 (blkOf lc) 3).get 25 == some 64 &&
    simpleFrom lc.ctx.f 1 4 && (uL35 lc [] (blkOf lc) 3).isEmpty && entryStoresOK lc g 3 &&
    argsOK lc g spills.toList 3 && cloBefore lc 3 && memTyL lc &&
    (constRo (symNames g)).isEmpty && !needs48 lc

/-- The checks of `lcFacts` as propositions. -/
theorem lc_spec {lc : LocCtx} (h : lcFacts lc = true) :
    checkG64L lc ps bs g = .ok (tab, ktOf lc) ∧ retRegsOK lc (ktOf lc) = true ∧
    ownOutRegs lc = [0] ∧ (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
    GenG2.noCalls lc = true ∧ noWbICall lc = true ∧ noMemEq lc = true ∧ lc.ctx.f.entry = 1 ∧
    1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some (blkOf lc) ∧
    (blkOf lc).values.size = 6 ∧ (blkOf lc).values[3]? = some 9 ∧
    lc.ctx.f.value? 9 = some (v9Of lc) ∧ (v9Of lc).op = .ARM64MOVDload ∧
    (∃ sI, enterListLoc env lc (locInit env lc args mem) ((blkOf lc).values.toList.take 3) =
      .ok sI ∧ sIIs sI = true ∧ loadOK lc sI (v9Of lc) = true) ∧
    (kAt lc (ktOf lc) 1 (blkOf lc) 3).get 0 = some 64 ∧
    (kAt lc (ktOf lc) 1 (blkOf lc) 3).get 25 = some 64 ∧
    simpleFrom lc.ctx.f 1 4 = true ∧ uL35 lc [] (blkOf lc) 3 = [] ∧
    entryStoresOK lc g 3 = true ∧ argsOK lc g spills.toList 3 = true ∧ cloBefore lc 3 = true ∧
    memTyL lc = true ∧ constRo (symNames g) = [] ∧ needs48 lc = false := by
  simp only [lcFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27⟩ := h
  have hc : checkG64L lc ps bs g = .ok (tab, ktOf lc) := by
    rw [← h2]
    exact eq_getOk h1
  have hb : lc.ctx.f.block? 1 = some (blkOf lc) := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h12
    simp [blkOf, hb]
  have hv : lc.ctx.f.value? 9 = some (v9Of lc) := by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h15
    simp [v9Of, hv]
  obtain ⟨sI, hsI, hsI'⟩ := GenG1.okThen_spec h17
  simp only [Bool.and_eq_true] at hsI'
  exact ⟨hc, h3, h4, h5, h6, h7, h8, h9, h10, h11, hb, h13, h14, hv, h16, ⟨sI, hsI, hsI'⟩, h18,
    h19, h20, List.isEmpty_iff.1 h21, h22, h23, h24, h25, List.isEmpty_iff.1 h26, h27⟩

/-! ## The environment -/

/-- `runLF` and `runL` of `f` run alike on `x = 7` and the funcval: out of fuel with none,
returning the same integer and memory with one unit. -/
def sameRun (tabs : Tables) (f : Func) : Bool :=
  isOOF (GoFV.Proof.runLF env tabs f args mem 0) && isOOF (runL env tabs f args mem 0) &&
    match GoFV.Proof.runLF env tabs f args mem 1, runL env tabs f args mem 1 with
    | .returned [.int .w64 a] m, .returned [.int .w64 a'] m' => a == a' && decide (m = m')
    | _, _ => false

/-- `sameRun` gives `NoNilFault` (`runLF_mono`, `runL_mono`). -/
theorem sameRun_spec {tabs : Tables} {f : Func} (h : sameRun tabs f = true) :
    GoFV.Proof.NoNilFault tabs f env args mem := by
  simp only [sameRun, Bool.and_eq_true] at h
  obtain ⟨⟨h0F, h0L⟩, h1⟩ := h
  have e1 : GoFV.Proof.runLF env tabs f args mem 1 = runL env tabs f args mem 1 ∧
      (runL env tabs f args mem 1).Defined := by
    split at h1
    · rename_i a m a' m' hF hL
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      rw [hF, hL]
      exact ⟨rfl, trivial⟩
    · cases h1
  intro fuel
  cases fuel with
  | zero => rw [isOOF_spec h0F, isOOF_spec h0L]
  | succ n =>
    rw [GoFV.Proof.runLF_mono (by omega : 1 ≤ n + 1) (e1.1 ▸ e1.2),
      GoFV.Proof.runL_mono (by omega : 1 ≤ n + 1) e1.2, e1.1]

/-- The closure context points into no nil page. -/
theorem cloH_nilBase : ¬ GoFV.Proof.SchedL.NilBase cloH := by
  rintro ⟨b, hb, hn⟩
  simp only [cloH, Arm64.addr, Option.some.injEq] at hb
  subst hb
  cases hn

/-- **The closure conjunct of `InitAvoids`**: the arguments, the funcval, the globals and the
closure context avoid every frame temporary. -/
theorem initAvoidsC : InitAvoids env args mem := by
  intro a n
  refine ⟨fun v h => ?_, fun b al h _ x hx => ?_, ?_, fun g hg x hx => ?_, fun c hc => ?_⟩
  · simp only [args, List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    trivial
  · simp only [mem, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [cloAlloc, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp [Byte.Avoids, codeP]
  · simp [mem, Mem.find?]
  · simp only [env, plRunEnv, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · simp only [Array.toList_replicate, List.mem_replicate] at hx
      rw [hx.2]
      trivial
    · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
      rw [hx]
      trivial
  · simp only [env, Option.some.injEq] at hc
    subst hc
    simp [cloH, Val.Avoids]

theorem wbPreC : GoFV.Proof.WB.WbPre env args mem := by
  refine ⟨⟨⟨{ data := #[.b 0, .b 0, .b 0, .b 0], writable := false }, by decide +kernel,
    rfl, by decide, fun i hi => ?_⟩, by decide +kernel⟩, plRunEnv_wbPre.2.1, plRunEnv_wbPre.2.2⟩
  match i, hi with
  | 0, _ => exact ⟨0, rfl⟩
  | 1, _ => exact ⟨0, rfl⟩
  | 2, _ => exact ⟨0, rfl⟩
  | 3, _ => exact ⟨0, rfl⟩

/-- **`VPre` of `env`** on `x = 7` and the funcval. -/
theorem env_vpre {k : List Nat} {ro : List (String × Alloc)} (hk : k = []) (hro : ro = [])
    (eq : List String × List String) : VPre k ro eq env args mem :=
  ⟨plRunEnv_mono, plRunEnv_frameSafe, initAvoidsC, plRunEnv_allocNonNil,
    by rw [hk]; exact DictArgs.nil args, wbPreC, plRunEnv_tempOblivious, plRunEnv_memOps,
    by rw [hro]; exact RoImage.nil (env := env) (plRunEnv_keeps Mem.KeepsRo.refl) mem,
    plRunEnv_keeps Mem.KeepsFrame.refl, plRunEnv_allocZero, plRunEnv_growLen, plRunEnv_ifaceEq eq⟩

/-! ## The machine side -/

theorem byteRel_b {ι' : Blk → Option (BitVec 64)} {x y : BitVec 8} (h : x = y) :
    ByteRel ι' (.b x) y := h

theorem byteRel_frag {ι' : Blk → Option (BitVec 64)} {p : Ptr} {i : Nat} {a : BitVec 64}
    {y : BitVec 8} (ha : ι' p.blk = some a) (hy : y = (a + p.off).extractLsb' (8 * i) 8) :
    ByteRel ι' (.frag p i) y := ⟨a, ha, hy⟩

/-- `memI` injected into `mmI` by `ι`: the funcval at `cloA`, the globals at
`ObjWhole.gAddr1`, `ObjWhole.gAddr2`, the frame blocks at their Phase 1 addresses. -/
theorem memInj : MemInj ι memI mmI where
  nil := rfl
  mapped := by
    intro b al h
    simp only [memI, List.mem_toArray, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;>
    exact ⟨_, rfl, fun _ => by decide, by decide⟩
  inj := by
    intro b al b' al' a a' h h' hne ha ha'
    simp only [memI, List.mem_toArray, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at h h'
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;>
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;>
    first | exact absurd rfl hne | (cases ha; cases ha'; decide)
  bytes := by
    refine ⟨fun _ _ => False, ?_⟩
    intro b al a h ha
    simp only [memI, cloAlloc, List.mem_toArray, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at h
    refine ⟨fun _ h => h.elim, fun _ _ h => h.elim, fun i hi _ => ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;> cases ha
    · have h16 : i < 16 := by simpa using hi
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
      all_goals first
        | exact byteRel_frag rfl (by decide)
        | exact byteRel_b (by decide)
        | omega
    · simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => exact byteRel_b (by decide)
    · simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ => exact byteRel_b (by decide)
    · simp at hi
    · simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => exact byteRel_b (by decide)
    · simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => trivial
    · simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => trivial

theorem sep {lc : LocCtx} (hk : (memI.blocks.toList.map (·.1)).Nodup) :
    KeysNodup memI ∧ SepFrom ι (StkAt (E0 lc)) memI := by
  refine ⟨hk, fun b al a _ _ y hy => ?_⟩
  rcases hy with ⟨h, -⟩ | ⟨k, off, h, -⟩ <;> cases h

theorem g49Env {lc : LocCtx} (hc : checkG64L lc ps bs g = .ok (tab, ktOf lc))
    (hav : (accessedVars lc).isEmpty = true) (hsl : (homeSlots lc).isEmpty = true)
    (hnc : GenG2.noCalls lc = true) (hwi : noWbICall lc = true) (hme : noMemEq lc = true)
    (hend : GenG2.symA ≠ endP GenG2.text ps.toList) (hso : symsOut = true) :
    G49Env lc g L ps (endP L.text ps.toList) tab (E0 lc) := by
  obtain ⟨-, -, -, -, hlt, -, -⟩ := checkG64L_cx hc
  have h2 : G2Env lc g L ps 0 tab (E0 lc) :=
    { lcEq := rfl
      link := rfl
      pcOf := rfl
      retOut := by
        intro p hp
        exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
      addr := addrAgree
      glob := fun y name abi hy => by
        have h := (Array.all_eq_true_iff_forall_mem.1 hso) _ (Array.mem_of_getElem? hy)
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        simp only [E0, ι, h.1, h.2, ↓reduceIte]
        rfl
      syms := by
        intro y
        have hs : L.sym y = GenG2.symA := rfl
        rw [hs]
        refine ⟨by decide, fun p hp => ?_⟩
        exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
      calls := fun _ id v hv hop => by
        have h1 : lc.ctx.f.valueTab[id]? = some (some v) := by
          have hv' : (lc.ctx.f.valueTab[id]?).join = some v := hv
          cases h : lc.ctx.f.valueTab[id]? with
          | none => rw [h] at hv'; cases hv'
          | some o => rw [h] at hv'; cases o <;> simp_all
        have h2 := (Array.all_eq_true_iff_forall_mem.1 hnc) _ (Array.mem_of_getElem? h1)
        simp [hop] at h2
      slot := fun k hk => by simp [List.isEmpty_iff.1 hsl] at hk
      extra := by decide
      frame := ⟨show 4096 + 8 ≤ (0x7fff0000 : BitVec 64).toNat by decide,
        show (0x7fff0000 : BitVec 64).toNat + 8 ≤ 2 ^ 64 by decide, fun k off h => by cases h⟩ }
  exact
    { env := {
        env := {
          env := {
            env := {
              env := ObjG7.g2Env_endP h2 (ObjG7.retOut_endP hlt) (fun _ => hend)
              vars := by
                intro x hx
                simp [List.isEmpty_iff.1 hav] at hx }
            wbs := fun _ _ _ hv => (noWbICall_spec hwi hv).1 }
          icalls := fun _ _ _ hv => (noWbICall_spec hwi hv).2 }
        memeqs := fun _ _ _ hv => noMemEq_spec hme hv }
      vars := by
        intro x hx
        simp [List.isEmpty_iff.1 hav] at hx }

/-- The machine-side premises of `verified_mach` on `adder.func1`. -/
theorem obj_premises :
    ObjEnv ps spills obj otab L ObjG7.base code (s0.x 30) ∧
    HookMap GenG2.H0 L ps.toList (ObjEnv.map otab ps L ObjG7.base) ∧
    MachEntry code ObjG7.base 8 s0 ∧ otab.autosize + 8 ≤ 8 ∧
    (s0.x 28).toNat + 32 ≤ 2 ^ 64 ∧ otab.check = none ∧
    GenG2.symA ≠ endP GenG2.text ps.toList ∧
    (∀ lc, EntryEnv (E0 lc) L ps.toList otab.autosize s0) ∧
    (∀ lc, ObjEnv.map otab ps L ObjG7.base ((E0 lc).pcOf 1 3) =
      ObjG7.base + BitVec.ofNat 64 (otab.offs[0]!)) ∧
    (memI.blocks.toList.map (·.1)).Nodup ∧ symsOut = true ∧ (∀ u, ICallOut L ps.toList u) := by
  have hf := obj_facts
  simp only [objFacts, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨hef, hchk⟩, hnp⟩, hnend⟩, hpc⟩, hkeys⟩, hso⟩, hni⟩ := hf
  obtain ⟨hO, hend⟩ := ObjG7.envFacts_spec hef
  have hfacts := hef
  simp only [ObjG7.envFacts, Bool.and_eq_true, beq_iff_eq] at hfacts
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, haz⟩, -⟩, -⟩, -⟩, hr40⟩, -⟩, -⟩, -⟩ := hfacts
  replace haz : otab.autosize = 0 := haz
  refine ⟨hO, hookMap_retLR fun _ => rfl,
    { pc := rfl, spAlign := by decide, room := by decide, lrOutside := hr40,
      gOutside := by decide, fp := by decide },
    (by rw [haz]; decide), (by decide),
    Option.isNone_iff_eq_none.1 hchk,
    hend, fun lc => ?_, fun _ => hpc, hkeys, hso, ObjG7.noICall_spec hni L⟩
  exact
    { sp := by rw [haz]; show (0x7fff0000 : BitVec 64) + BitVec.ofInt 64 0 = 0x7fff0000; decide
      g := rfl
      lr := rfl
      fp := rfl
      fp0 := by decide
      framed := by rw [haz]; rfl
      lrOut := by
        refine ⟨fun hpa => ?_, hnend⟩
        obtain ⟨p, hp, h⟩ := hpa
        exact hnp p hp h }

/-! ## The run's premises -/

/-- G54's premises of a `MOVDload`: G3's load premise, every other one vacuous. -/
theorem g54Pre_load {lc : LocCtx} {s : LocState} {v : Value} (hop : v.op = .ARM64MOVDload)
    (hl : ∀ as n sg, loadOp? v.op = some (as, n, sg) → ∀ a x, v.args[0]? = some a →
      s.read lc a = .ok x → ∃ p mm bs, symAddr lc.ctx v x = some p ∧ s.mem = .mem mm ∧
        mm.read p n = some bs ∧
        (lc.ty v.id = .bool → ∀ y, mm.load (.int .w8) p = .int .w8 y → y.toNat < 2)) :
    G54Pre lc s v := by
  have hne : ∀ o : Op, o ≠ .ARM64MOVDload → v.op ≠ o := fun o h h' => h (h'.symm.trans hop)
  have h46 : G46Pre lc s v := by
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, hl, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩
    · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
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
  refine ⟨⟨⟨⟨h46, fun _ _ _ _ hp => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩, fun h => ?_⟩,
    fun h => ?_, fun h => ?_⟩
  · rw [hop] at hp; cases hp
  · rcases h with h | h <;> exact absurd h (hne _ (by decide))
  all_goals exact absurd h (hne _ (by decide))

theorem pre64_load {lc : LocCtx} {s : LocState} {v : Value} (hop : v.op = .ARM64MOVDload) :
    FReloadPre lc s v ∧ QLoadPre lc s v ∧ MemEqPre lc s v :=
  ⟨fun h => absurd (h.symm.trans hop) (by decide), ⟨fun h => absurd (h.symm.trans hop) (by decide),
    fun h => absurd (h.symm.trans hop) (by decide)⟩, fun h => absurd (h.symm.trans hop) (by decide)⟩

/-- A run from value `i0 > 0` of a block no edge enters is at its start state when back at
`(b0, i0)` (`ObjEndToEndAtSP.lreach_start`, which is stated at that witness's layout). -/
private theorem lreach_at_start {env' : Env} {lc : LocCtx} {b0 : ID} {i0 : Nat}
    {s0' : LocState} (hi0 : 0 < i0)
    (hno : ∀ b' blk', lc.ctx.f.block? b' = some blk' → ∀ e ∈ blk'.succs.toList, e.b ≠ b0)
    {b : ID} {i : Nat} {s : LocState} (h : LReach env' lc b0 i0 s0' b i s) :
    b = b0 → i = i0 → s = s0' := by
  induction h with
  | refl => intro _ _; rfl
  | val hr _ _ _ _ _ =>
    intro hb hi
    rcases lreach_cases hr with ⟨-, h⟩ | ⟨b', blk', e, hb', he, heb⟩
    · omega
    · exact absurd (heb.trans hb) (hno b' blk' hb' e he)
  | term _ _ _ _ => intro _ hi; omega

/-- **`RunPre` of `adder.func1`** from `(b1, 3)`: the load `v9` at `sI`, the only state the run
reaches there, reads valid bytes (`loadOK`); every later value is a simple op; `CloOK` holds at
every reached state by `cloOK_of_cloBefore`. -/
theorem runPreClo {lc : LocCtx} {E0' : MatchEnv} {blk : Block} {sI : LocState} {v : Value}
    {ret : BitVec 64} (hentry : lc.ctx.f.entry = 1) (hsim : simpleFrom lc.ctx.f 1 4 = true)
    (hb : lc.ctx.f.block? 1 = some blk) (hi3 : blk.values[3]? = some 9)
    (hv : lc.ctx.f.value? 9 = some v) (hop : v.op = .ARM64MOVDload)
    (hld : loadOK lc sI v = true) (hcb : cloBefore lc 3 = true) :
    RunPre env GenG2.H0 lc g L ret E0' lc.ctx.f.entry 3 sI := by
  have hblk := simpleFrom_blk hsim
  have hno : ∀ b' blk', lc.ctx.f.block? b' = some blk' → ∀ e ∈ blk'.succs.toList, e.b ≠ 1 :=
    fun b' blk' h => (hblk b' blk' h).2.2.1
  intro b i s blk' hr hb'
  have hC : ∀ id v', blk'.values[i]? = some id → lc.ctx.f.value? id = some v' →
      ∀ E m, CloOK E s v' m := fun id v' hi hval E m =>
    cloOK_of_cloBefore hcb hr hb' hi hval E m
  rw [hentry] at hr
  obtain ⟨hz, hnz, -, hv'⟩ := hblk b blk' hb'
  have hpos : b = 1 → 3 ≤ i := by
    rcases lreach_cases hr with ⟨-, h⟩ | ⟨b', blk'', e, hb'', he, rfl⟩
    · exact fun _ => h
    · exact fun h => absurd h (hno b' blk'' hb'' e he)
  refine ⟨fun id v' hi hval => ?_, fun _ hk => ?_⟩
  · have hclo := hC id v' hi hval
    rcases hv' i id v' hi hval with ⟨h1, h2⟩ | hs
    · have hi' : i = 3 := by have := hpos h1; omega
      subst h1 hi'
      have hsI := lreach_at_start (by decide : 0 < 3) hno hr rfl rfl
      subst hsI
      rw [hb] at hb'
      cases hb'
      rw [hi3] at hi
      cases hi
      rw [hv] at hval
      cases hval
      have hne : ∀ o : Op, o ≠ .ARM64MOVDload → v.op ≠ o := fun o h h' => h (h'.symm.trans hop)
      refine ⟨.inl (by rw [hop]; rfl), fun s' _ =>
        ⟨⟨g54Pre_load hop (loadOK_spec hld), pre64_load hop⟩, fun E m _ _ =>
          ⟨fun h => absurd h (hne _ (by decide)), fun h => absurd h (hne _ (by decide)), ?_,
            fun h => absurd h (hne _ (by decide)), hclo E m, fun h => absurd h (hne _ (by decide)),
            fun h => absurd h (hne _ (by decide))⟩⟩⟩
      intro n _ _ _ _ _ _ _ _ _ hn
      rw [hop] at hn
      cases hn
    · have hs' := hs
      simp only [simpleOp, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hs'
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hc⟩, hic⟩, hwb⟩, -⟩, hen⟩, -⟩,
        -⟩, hgg⟩, hme⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hs'
      refine ⟨.inl (by simp [entryOp24, hen]), fun s' _ => ⟨⟨g54Pre_simple hs s, pre64_simple hs s⟩,
        fun E m _ _ =>
        ⟨fun h => absurd h hc, fun h => absurd h hc, ?_, fun h => absurd h hwb,
          hclo E m, fun h => absurd h hgg, fun h => absurd h hme⟩⟩⟩
      intro n _ _ _ _ _ _ _ _ _ hn
      rw [hic] at hn
      cases hn
  · rcases hk with hk | hk
    · exact absurd hk hz
    · exact absurd hk hnz

/-- The machine word of the 64-bit integer `12` is `12`. -/
theorem valRel_12 {ι' : Blk → Option (BitVec 64)} {r : BitVec 64}
    (h : ValRel ι' (.int .w64 12) r) : r = 12 := by
  rcases h with h | ⟨hb, -⟩
  · exact h
  · exact absurd (by decide) hb

/-! ## The witness -/

/-- What compiled evaluation checks: the export parses, the pipeline is `fullyVerified` with
`schedule` inputs that run as `runL` (`sameRun`), free of pointer-shaped parameter pieces and
checked pointers, `refsLive` holds of its output and `lcFacts` of `liveCtx` of it, whose body
returns `12`; the generic `run` returns `12`, and the input has no dictionary parameter and no
read-only symbol. -/
def e2eFacts : Bool :=
  ((verifiedPipelineFull penv f0 0 sec0.zvar dcl).toOption.map fun r =>
      r.fullyVerified &&
        r.nnf.all (fun x => sameRun x.1 x.2 && noArgPtrB x.1 x.2 && noNilPtrB x.1 x.2) &&
        refsLive (LocCtx.make r.st.tables r.st.func) &&
        lcFacts (liveCtx (LocCtx.make r.st.tables r.st.func)) &&
        isRet12 (runLoopLoc env (liveCtx (LocCtx.make r.st.tables r.st.func)) 4
          (locInit env (liveCtx (LocCtx.make r.st.tables r.st.func)) args mem)
          (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.f.entry)) == some true &&
    isRet12 (GoFV.SSA.run env penv.tables f0 args mem 5) &&
    (NilCheck.dictParams penv.tables f0).isEmpty && (pipelineRo penv f0).isEmpty

theorem e2e_facts : e2eFacts = true := by
  native_decide

/-- **Non-vacuity of `verified_mach` in a closure**: on `adder.func1` with the closure context
`cloH` (the funcval `heap 1`, capturing `k = 5`) and `x = 7`, the verified pipeline returns a
`fullyVerified` state, the generic `run` returns `12`, and `verified_mach` applies with every
premise discharged: a `runLoc` of the allocated function refines the `run`, it is `finish` of its
body's defined outcome, and when the body returns, `runMach` of the linked words from the
function's entry (`X26` holding the closure object's address) returns to the caller's `0x40`
(`MachRet`) with the results in `X0` (`ResultRel`); the body returns `12`, which the machine
returns in `X0`. -/
theorem verified_mach_clo_witness :
    env.closure = some cloH ∧
    ∃ r, verifiedPipelineFull penv f0 0 sec0.zvar dcl = .ok r ∧ r.fullyVerified = true ∧
      (∃ m, GoFV.SSA.run env penv.tables f0 args mem 5 = .returned [.i64 12] m) ∧
      ∃ fuel', OutcomeRefines 0 (GoFV.SSA.run env penv.tables f0 args mem 5)
          (runLoc env r.st.tables r.st.func args mem fuel') ∧
        ∃ raw, runLoopLoc env (liveCtx (LocCtx.make r.st.tables r.st.func)) fuel'
            (locInit env (liveCtx (LocCtx.make r.st.tables r.st.func)) args mem)
            (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.f.entry = raw ∧
          runLoc env r.st.tables r.st.func args mem fuel' =
            finish env (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.outs
              (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.defers
              (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.act raw ∧
          raw.Defined ∧
          (∀ rs mm, raw = .returned rs mm →
            ∃ E t' n, (E0 (liveCtx (LocCtx.make r.st.tables r.st.func))).Extends E ∧
              runMach GenG2.H0 code (s0.x 30) n s0 = .returned t' ∧
              MachRet s0 t' ∧ ResultRel E [0] rs mm t') ∧
          ∃ mm, raw = .returned [.i64 12] mm ∧
            ∃ E t' n, (E0 (liveCtx (LocCtx.make r.st.tables r.st.func))).Extends E ∧
              runMach GenG2.H0 code (s0.x 30) n s0 = .returned t' ∧
              MachRet s0 t' ∧ t'.x 0 = 12 ∧ ResultRel E [0] [.i64 12] mm t' := by
  have hf := e2e_facts
  simp only [e2eFacts, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hf
  obtain ⟨⟨⟨hp, hrun⟩, hdict⟩, hro⟩ := hf
  obtain ⟨hO, hH, hME, hroom, hg, hnone, hend, hEE, hpcF, hkeys, hso, hic⟩ := obj_premises
  cases hpe : verifiedPipelineFull penv f0 0 sec0.zvar dcl with
  | error e => rw [hpe] at hp; cases hp
  | ok r =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true] at hp
    obtain ⟨⟨⟨⟨hv, hn⟩, hrl⟩, hC⟩, hF⟩ := hp
    obtain ⟨hcL, hrok, houts, hav, hsl, hnc, hwi, hme, hentry, hbm, hb1, hsz, hi3, hv9, hop,
      ⟨sI, hsI, hsIIs, hld⟩, hk0, hk25, hsim, hu, hes, hargs, hcb, hmt, hcr, hn48⟩ := lc_spec hC
    obtain ⟨hregs, hflags, hslots, hmem⟩ := sIIs_spec hsIIs
    have hx2 : ∀ x ∈ r.nnf,
        (sameRun x.1 x.2 = true ∧ noArgPtrB x.1 x.2 = true) ∧ noNilPtrB x.1 x.2 = true :=
      fun x hx => by
        have := List.all_eq_true.1 hn x hx
        simpa only [Bool.and_eq_true] using this
    have hnn : ∀ x ∈ r.nnf, GoFV.Proof.NoNilFault x.1 x.2 env args mem := fun x hx =>
      sameRun_spec (hx2 x hx).1.1
    have hap : ∀ x ∈ r.nnf, GoFV.Proof.ArgPtrsOK x.1 x.2 env args mem := fun x hx =>
      argPtrsOK_of_none (hx2 x hx).1.2 env args mem fun c hc => by
        simp only [env, Option.some.injEq] at hc
        subst hc
        exact cloH_nilBase
    have hnp : ∀ x ∈ r.nnf, GoFV.Proof.NilPtrsOK x.1 x.2 env args mem := fun x hx =>
      nilPtrsOK_of_none (hx2 x hx).2 env args mem
    obtain ⟨m0, hrun0⟩ := isRet12_spec hrun
    have hd : (GoFV.SSA.run env penv.tables f0 args mem 5).Defined := by
      rw [hrun0]; trivial
    have hc64 : checkG64 (LocCtx.make r.st.tables r.st.func) ps bs g = .ok (tab, ktOf
        (liveCtx (LocCtx.make r.st.tables r.st.func))) := by
      simpa [checkG64, hrl] using hcL
    have hE := g49Env hcL hav hsl hnc hwi hme hend hso
    have hent : EntryMatch (E0 (liveCtx (LocCtx.make r.st.tables r.st.func))) g
        (InWins L (E0 (liveCtx (LocCtx.make r.st.tables r.st.func))).sp
          (pendWins (liveCtx (LocCtx.make r.st.tables r.st.func)) g)) sI s0 :=
      { regs := by
          intro q v hv
          by_cases h0 : q = 0
          · subst h0
            rw [(hregs 0 v hv).1 rfl]
            refine ⟨fun q hq => ?_, fun q hq => by simp [objV?] at hq⟩
            simp only [objX?] at hq
            cases hq
            exact ⟨fun h => by rcases h with h | h | h | h <;> exact absurd h (by decide),
              Or.inl (by decide)⟩
          · by_cases h25 : q = 25
            · subst h25
              rw [(hregs 25 v hv).2.1 rfl]
              refine ⟨fun q hq => ?_, fun q hq => by simp [objV?] at hq⟩
              simp only [objX?] at hq
              cases hq
              exact ⟨fun h => by rcases h with h | h | h | h <;> exact absurd h (by decide),
                Or.inl (by decide)⟩
            · rw [(hregs q v hv).2.2 h0 h25]
              exact ⟨fun _ _ => ⟨fun _ => rfl, trivial⟩, fun _ _ => trivial⟩
        flags := hflags
        stack := fun k v h => by rw [hslots] at h; cases h
        mem := ⟨memI, hmem, mmI, memInj, fun _ _ => rfl⟩ }
    have hinv : G3Inv (E0 (liveCtx (LocCtx.make r.st.tables r.st.func)))
        (liveCtx (LocCtx.make r.st.tables r.st.func))
        (kAt (liveCtx (LocCtx.make r.st.tables r.st.func))
          (ktOf (liveCtx (LocCtx.make r.st.tables r.st.func)))
          (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.f.entry
          (blkOf (liveCtx (LocCtx.make r.st.tables r.st.func))) 3) sI :=
      { core := by
          refine ⟨fun q v c _ hv hc => ?_, memI, hmem, sep hkeys⟩
          by_cases h0 : q = 0
          · subst h0
            rw [(hregs 0 v hv).1 rfl]
            rw [hentry, hk0] at hc
            cases hc
            rfl
          · by_cases h25 : q = 25
            · subst h25
              rw [(hregs 25 v hv).2.1 rfl]
              rw [hentry, hk25] at hc
              cases hc
              rfl
            · rw [(hregs q v hv).2.2 h0 h25]
              trivial
        slots := by intro k v h; rw [hslots] at h; cases h }
    have hRP := runPreClo (E0' := E0 (liveCtx (LocCtx.make r.st.tables r.st.func)))
      (ret := endP L.text ps.toList) hentry hsim hb1 hi3 hv9 hop hld hcb
    rw [← hentry] at hb1 hbm hpcF
    obtain ⟨fuel', href, raw, hraw, hfin, hdef, hret, -⟩ :=
      verified_mach hpe hv (env_vpre hdict hro _) hnn hap hnp hd rfl hc64 hn48 hO hH hic hrok
        hME hroom hg
        (fun _ _ _ h => by rw [hnone] at h; cases h) (fun _ _ _ h => by rw [hnone] at h; cases h)
        hE (hEE _) hb1 hbm (by rw [hsz]; decide) hsI hes hargs hent
        (fun _ _ _ h => by rw [hnone] at h; cases h) hinv hu (hpcF _) hRP (fun _ => hmt)
        (by rw [hcr]; intro n a h; cases h)
    rw [houts] at hret
    obtain ⟨mF, hF⟩ := isRet12_spec hF
    have hraw12 : raw = .returned [.i64 12] mF := by
      rw [← hraw]
      rcases Nat.le_total fuel' 4 with h | h
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
        rw [hk] at hF
        rw [← GoFV.Proof.runLoopLoc_mono env _ fuel' k _ _ (by rw [hraw]; exact hdef)]
        exact hF
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [GoFV.Proof.runLoopLoc_mono env _ 4 k _ _ (by rw [hF]; trivial)]
        exact hF
    obtain ⟨E, t', n, hx, hrm, hX, hRes⟩ := hret _ _ hraw12
    exact ⟨rfl, r, rfl, hv, ⟨m0, hrun0⟩, fuel', href, raw, hraw, hfin, hdef, hret, mF, hraw12,
      E, t', n, hx, hrm, hX,
      valRel_12 ((hRes.regs 0 _ 0 rfl rfl).resolve_right fun h => absurd h.1 (by decide)).2,
      hRes⟩

end GoFV.Proof.Witness.ObjEndToEndClo
