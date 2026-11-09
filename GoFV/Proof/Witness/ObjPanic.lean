import GoFV.Proof.Obj.Whole
import GoFV.Proof.Witness.ObjWhole
import GoFV.Proof.Witness.GenG9

/-!
# Non-vacuity witnesses: panics down to the machine words (`obj_whole_panic`, `g30_callPanic`)

**A nil check that panics, whole function.** `(*A).g` of `test/method` (`GenG7`: `checkG30`
accepts it with the tables of `checkG7`; `ObjG7`: `checkObj` accepts its assembled words, a
frameless leaf without a stack check), the wrapper whose entry block `b2` runs `v5 = ArgIntReg`
(`R0`), `v1 = InitMem`, `v6 = LoweredNilCheck v5 v1` (`MOVB (R0), R27`) and returns. From
`runLoc`'s first state on the nil receiver in the Phase 1 test environment `plRunEnv` (`locInit`:
the frame memory holds the environment's globals, the outgoing-arguments area, the receiver's
image and a temporary), the entry values run to `sI` (`R0 = 0`), and the nil check panics with
`nilDeref`. The machine starts at the function's entry `base` (`MachEntry`: `SP = 0x7fff0000`,
`X0 = 0`, `g = 0x9000`, the caller's `LR = 0x40` outside the code, `R29 = SP - 8`, the memory 0).
`obj_whole_panic` gives a `runMach` of the linked words that panics with `nilDeref` (the `MOVB` at
address 0, `sigpanic`). The run reaches no state but `sI` (`lreach_of_panicAt`), where `RunPre`
holds (the nil check's `NilPre` on a nil pointer) and `RunPanicPre` is the nil check's.

**A static call whose callee panics.** `fint64to32` (`GenG9`: `checkG30` accepts it), whose
`v8 = CALLstatic v6 v1` calls `runtime.fintto32`: in the environment `envP` the callee panics with
`nilDeref`; with the hook `Hp` that panics alike at the callee's symbol (`CallPanicOK`),
`g30_callPanic` gives the P0 run through the `CALL` to the symbol, where `runProg` panics with the
same panic (`PPanics`).

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`;
`panic_obj_facts`, `panic_lc_facts`, `callPanic_facts`).
-/

namespace GoFV.Proof.Witness.ObjPanic

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen GoFV.Proof.Obj
open GoFV.Proof (enterListLoc)

/-! ## `(*A).g` with a nil receiver -/

abbrev ps : Array Prog := GenG7.ps
abbrev L : Link := GenG7.L

/-- The nil receiver. -/
def args : List Val := [.ptr ⟨.nil, 0⟩]

/-- Block `b2` of `lc`. -/
def blk (lc : LocCtx) : Block := (lc.ctx.f.block? 2).getD default

/-- The nil check `v6`, value 2 of `b2`. -/
def vNil (lc : LocCtx) : Value := (lc.ctx.f.value? 6).getD default

/-- The frame memory: `plRunEnv`'s globals, the outgoing-arguments area, the receiver's image (the
nil pointer's bytes), a temporary. -/
def memI : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] }),
      (.global "runtime.writeBarrier", { data := #[.b 0, .b 0, .b 0, .b 0], writable := false }),
      (.outargs 0, { data := #[] }),
      (.local 0 3, { data := #[.frag ⟨.nil, 0⟩ 0, .frag ⟨.nil, 0⟩ 1, .frag ⟨.nil, 0⟩ 2,
        .frag ⟨.nil, 0⟩ 3, .frag ⟨.nil, 0⟩ 4, .frag ⟨.nil, 0⟩ 5, .frag ⟨.nil, 0⟩ 6,
        .frag ⟨.nil, 0⟩ 7] }),
      (.temp 0 4, { data := #[.poison, .poison, .poison, .poison, .poison, .poison, .poison,
        .poison] })] }

/-- The machine memory: 0. -/
def mm : Memory := fun _ => 0

/-- The activation: frameless, `SP = 0x7fff0000`, `g = 0x9000`, `LR = 0x40`, `FP = SP - 8`. -/
def E0 (lc : LocCtx) : MatchEnv :=
  { lc, ι := ObjWhole.ι, sp := 0x7fff0000, slot := fun _ => none, g := 0x9000, lr := 0x40,
    fp := 0x7fff0000 - 8, framed := false, pcOf := pcOfTab GenG2.text ps.toList GenG7.tab }

/-- The machine at the function's entry: `X0 = 0`. -/
def s0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then 0x7fff0000 - 8
      else if k = 30 then 0x40 else 0,
    sp := 0x7fff0000, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩, pc := ObjG7.base,
    mem := mm }

/-- The 64-bit integer 0. -/
def isZero64 : Val → Bool
  | .int .w64 x => x == 0
  | _ => false

theorem isZero64_spec {v : Val} (h : isZero64 v = true) : v = .int .w64 0 := by
  unfold isZero64 at h
  split at h
  · simp only [beq_iff_eq] at h
    subst h; rfl
  · cases h

/-- `R0` holds the integer 0, every other register `poison`; no flags, no slot, the frame
memory. -/
def sIIs (s : LocState) : Bool :=
  (List.range s.regs.size).all (fun r =>
      match s.regs[r]? with
      | some v => if r = 0 then isZero64 v else ObjWhole.isPoison v
      | none => true) &&
    ObjWhole.isPoison s.flags && s.slots.isEmpty &&
    match s.mem with
    | .mem m => decide (m = memI)
    | _ => false

theorem sIIs_spec {s : LocState} (h : sIIs s = true) :
    (∀ r v, s.regs[r]? = some v → (r = 0 → v = .int .w64 0) ∧ (r ≠ 0 → v = .poison)) ∧
      s.flags = .poison ∧ s.slots = [] ∧ s.mem = .mem memI := by
  simp only [sIIs, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.isEmpty_iff] at h
  obtain ⟨⟨⟨hr, hf⟩, hs⟩, hm⟩ := h
  refine ⟨fun r v hv => ?_, ?_, hs, ?_⟩
  · have hlt := (Array.getElem?_eq_some_iff.1 hv).1
    have := hr r hlt
    rw [hv] at this
    constructor
    · rintro rfl
      exact isZero64_spec (by simpa using this)
    · intro h0
      simp only [h0, ↓reduceIte, ObjWhole.isPoison] at this
      split at this
      · rfl
      · cases this
  · unfold ObjWhole.isPoison at hf
    split at hf
    · assumption
    · cases hf
  · split at hm
    · simp only [decide_eq_true_eq] at hm
      subst hm; assumption
    · cases hm

/-- A `runLoc` step that panics with `nilDeref`. -/
def isNilPanic : Res LocState → Bool
  | .panic .nilDeref _ => true
  | _ => false

theorem isNilPanic_spec {r : Res LocState} (h : isNilPanic r = true) :
    ∃ mm', r = .panic .nilDeref mm' := by
  unfold isNilPanic at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- An outcome that panics with `nilDeref`. -/
def isNilPanicked : Outcome → Bool
  | .panicked .nilDeref _ => true
  | _ => false

theorem isNilPanicked_spec {o : Outcome} (h : isNilPanicked o = true) :
    ∃ mm', o = .panicked .nilDeref mm' := by
  unfold isNilPanicked at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- The nil check's pointer is in the nil block (`NilPre` holds vacuously). -/
def nilArg (lc : LocCtx) (s : LocState) : Bool :=
  (vNil lc).args[0]?.all fun a =>
    match s.read lc a with
    | .ok x => (Arm64.addr x 0#64).all (·.blk == .nil)
    | _ => true

/-- No symbol of `(*A).g` is one of `plRunEnv`'s globals. -/
def symsOut : Bool :=
  GenG7.g.syms.all fun x =>
    x.1.toStringLossy != "main.g" && x.1.toStringLossy != "runtime.writeBarrier"

/-- What compiled evaluation checks of the machine side: `checkObj` accepts with no frame and no
stack check, the linked code, no `CALL (Rn)`, the return address `0x40` is no P0 address, the P0
address of the entry's value 2 maps to the body's start, and `memI`'s keys are distinct. -/
def objFacts : Bool :=
  ObjG7.envFacts ps ObjG7.gSpills ObjG7.gObj && ObjG7.gTab.check.isNone &&
    ps.toList.all (fun p => addrP GenG2.text p.id != 0x40) &&
    (0x40 : BitVec 64) != endP GenG2.text ps.toList &&
    ObjEnv.map ObjG7.gTab ps L ObjG7.base (pcOfTab GenG2.text ps.toList GenG7.tab 2 2) ==
      ObjG7.base + BitVec.ofNat 64 (ObjG7.gTab.offs[0]!) &&
    decide ((memI.blocks.toList.map (·.1)).Nodup) && symsOut && ObjG7.noICall ps &&
    GenG7.g.syms.all (· != pbSym)

theorem panic_obj_facts : objFacts = true := by
  native_decide

/-- What compiled evaluation checks of `runLoc` on `(*A).g`: `checkG30` accepts it with `checkG7`'s
tables; no frame variable, home slot, static or indirect call, write barrier or `LoweredMemEq`; the
entry is `b2`, whose value 2 is the nil check `v6`; the entry values run from `runLoc`'s first
state on the nil receiver to `R0 = 0` and the frame memory, where `R0` has class 64, no upper-bit
fact is carried (`uL`) and `v6` panics with `nilDeref` on a pointer in the nil block; the whole
run panics with `nilDeref`. -/
def lcFacts (lc : LocCtx) : Bool :=
  (checkG30 lc ps GenG7.bs GenG7.g).toOption == some (GenG7.tab, GenG7.kt) &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty && GenG2.noCalls lc &&
    ObjWhole.noWbICall lc && lc.ctx.f.entry == 2 && lc.ctx.f.blocks.toList.contains 2 &&
    (lc.ctx.f.block? 2).isSome && (lc.ctx.f.value? 6).isSome && (blk lc).values[2]? == some 6 &&
    (vNil lc).op == .ARM64LoweredNilCheck && 2 < (blk lc).values.size &&
    GenG1.okThen (enterListLoc GoFV.Proof.Witness.plRunEnv lc
      (locInit GoFV.Proof.Witness.plRunEnv lc args {}) ((blk lc).values.toList.take 2))
      (fun s => sIIs s && nilArg lc s &&
        isNilPanic (stepLoc GoFV.Proof.Witness.plRunEnv lc s (vNil lc))) &&
    (kAt lc GenG7.kt 2 (blk lc) 2).get 0 == some 64 &&
    isNilPanicked (runLoopLoc GoFV.Proof.Witness.plRunEnv lc 4
      (locInit GoFV.Proof.Witness.plRunEnv lc args {}) lc.ctx.f.entry) &&
    ObjWhole.noMemEq lc && (uL lc (blk lc) 2).isEmpty

theorem panic_lc_facts : lcFacts GenG7.lc = true := by
  native_decide

/-! ## The activation -/

theorem memInj : MemInj ObjWhole.ι memI mm where
  nil := rfl
  mapped := by
    intro b al h
    simp only [memI, List.mem_toArray, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨_, rfl, fun _ => by decide, by decide⟩
  inj := by
    intro b al b' al' a a' h h' hne ha ha'
    simp only [memI, List.mem_toArray, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at h h'
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | exact absurd rfl hne | (cases ha; cases ha'; decide)
  bytes := by
    refine ⟨fun _ _ => False, ?_⟩
    intro b al a h ha
    simp only [memI, List.mem_toArray, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at h
    refine ⟨fun _ h => h.elim, fun _ _ h => h.elim, fun i hi _ => ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [ByteRel, mm]
    · simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ => simp [ByteRel, mm]
    · simp at hi
    · simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
        exact ⟨0, rfl, by simp [mm]⟩
    · simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => trivial

theorem sep {lc : LocCtx} (hk : (memI.blocks.toList.map (·.1)).Nodup) :
    KeysNodup memI ∧ SepFrom ObjWhole.ι (StkAt (E0 lc)) memI := by
  refine ⟨hk, fun b al a _ _ y hy => ?_⟩
  rcases hy with ⟨h, -⟩ | ⟨k, off, h, -⟩ <;> cases h

theorem g28Env {lc : LocCtx}
    (hc : checkG30 lc ps GenG7.bs GenG7.g = .ok (GenG7.tab, GenG7.kt))
    (hav : (accessedVars lc).isEmpty = true) (hsl : (homeSlots lc).isEmpty = true)
    (hnc : GenG2.noCalls lc = true) (hwi : ObjWhole.noWbICall lc = true)
    (hme : ObjWhole.noMemEq lc = true)
    (hend : GenG2.symA ≠ endP GenG2.text ps.toList) (hso : symsOut = true) :
    G28Env lc GenG7.g L ps (endP L.text ps.toList) GenG7.tab (E0 lc) := by
  obtain ⟨-, -, -, -, hlt, -, -⟩ := checkG30_cx hc
  have h2 : G2Env lc GenG7.g L ps 0 GenG7.tab (E0 lc) :=
    { lcEq := rfl
      link := rfl
      pcOf := rfl
      retOut := by
        intro p hp
        exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
      addr := ObjWhole.addrAgree
      glob := fun y name abi hy => by
        have h := (Array.all_eq_true_iff_forall_mem.1 hso) _ (Array.mem_of_getElem? hy)
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        simp only [E0, ObjWhole.ι, h.1, h.2, ↓reduceIte]
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
            env := ObjG7.g2Env_endP h2 (ObjG7.retOut_endP hlt) (fun _ => hend)
            vars := by
              intro x hx
              simp [List.isEmpty_iff.1 hav] at hx }
          wbs := fun _ _ _ hv => (ObjWhole.noWbICall_spec hwi hv).1 }
        icalls := fun _ _ _ hv => (ObjWhole.noWbICall_spec hwi hv).2 }
      memeqs := fun _ _ _ hv => ObjWhole.noMemEq_spec hme hv }

/-- No bounds panic call: `BoundsOK` holds of any hook. -/
theorem boundsOK_none {H : Hooks} {g : G2In} {L : Link} {ps : List Prog}
    (h : g.syms.all (· != pbSym) = true) : BoundsOK H g L ps := by
  intro k _ y _ _ _ _ hy
  have := (Array.all_eq_true_iff_forall_mem.1 h) _ (Array.mem_of_getElem? hy)
  simp at this

/-- `GenG2.H0` never panics. -/
theorem hookPanicMap_H0 {L : Link} {ps : List Prog} {f : BitVec 64 → BitVec 64} :
    HookPanicMap GenG2.H0 L ps f := by
  intro s t e s' _ _ _ h
  cases h

/-- **`(*A).g` panics down to the machine words, in any `runLoc` context meeting `lcFacts`**:
`runLoc`'s run from its first state on the nil receiver panics with `nilDeref`, and `runMach` of
the linked words from the function's entry panics with `nilDeref` (`obj_whole_panic`). -/
theorem panic_of {lc : LocCtx} (hf : lcFacts lc = true) :
    ∃ mm', runLoopLoc GoFV.Proof.Witness.plRunEnv lc 4
        (locInit GoFV.Proof.Witness.plRunEnv lc args {}) lc.ctx.f.entry = .panicked .nilDeref mm' ∧
      ∃ n t', runMach GenG2.H0 ObjG7.gCode 0x40 n s0 = .panicked .nilDeref t' := by
  -- the machine side
  have hof := panic_obj_facts
  simp only [objFacts, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    decide_eq_true_eq] at hof
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hef, hchk⟩, hnp⟩, hnend⟩, hpc⟩, hkeys⟩, hso⟩, hni⟩, hnpb⟩ := hof
  obtain ⟨hO, hend⟩ := ObjG7.envFacts_spec hef
  have hfacts := hef
  simp only [ObjG7.envFacts, Bool.and_eq_true, beq_iff_eq] at hfacts
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, haz⟩, -⟩, -⟩, -⟩, hr40⟩, -⟩, -⟩, -⟩ := hfacts
  replace haz : ObjG7.gTab.autosize = 0 := haz
  have hME : MachEntry ObjG7.gCode ObjG7.base 8 s0 :=
    { pc := rfl, spAlign := by decide, room := by decide, lrOutside := hr40,
      gOutside := by decide, fp := by decide }
  have hEE : EntryEnv (E0 lc) L ps.toList ObjG7.gTab.autosize s0 :=
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
  -- the `runLoc` side
  have hlf := hf
  simp only [lcFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hlf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, hav⟩, hsl⟩, hnc⟩, hwi⟩, hentry⟩, hbm⟩, hbs⟩, hv6s⟩, hi2⟩, hop⟩,
    hsz⟩, hpre⟩, hk0⟩, hrunP⟩, hme⟩, hu⟩ := hlf
  have hc : checkG30 lc ps GenG7.bs GenG7.g = .ok (GenG7.tab, GenG7.kt) := by
    revert hres; cases checkG30 lc ps GenG7.bs GenG7.g <;> simp [Except.toOption]
  have hb2 : lc.ctx.f.block? 2 = some (blk lc) := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  have hv6 : lc.ctx.f.value? 6 = some (vNil lc) := by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv6s
    simp [vNil, hv]
  obtain ⟨sI, hsI, hsIx⟩ := GenG1.okThen_spec hpre
  simp only [Bool.and_eq_true] at hsIx
  obtain ⟨⟨hsIIs, hnarg⟩, hpan⟩ := hsIx
  obtain ⟨e0, hpan⟩ := isNilPanic_spec hpan
  obtain ⟨hregs, hflags, hslots, hmem⟩ := sIIs_spec hsIIs
  obtain ⟨mm', hrun⟩ := isNilPanicked_spec hrunP
  have hsz' : 2 < (blk lc).values.size := of_decide_eq_true hsz
  have hu' : uL lc (blk lc) 2 = [] := List.isEmpty_iff.1 hu
  replace hb2 : lc.ctx.f.block? lc.ctx.f.entry = some (blk lc) := by rw [hentry]; exact hb2
  replace hbm : lc.ctx.f.entry ∈ lc.ctx.f.blocks.toList := by rw [hentry]; exact hbm
  replace hk0 : (kAt lc GenG7.kt lc.ctx.f.entry (blk lc) 2).get 0 = some 64 := by
    rw [hentry]; exact hk0
  replace hpc : ObjEnv.map ObjG7.gTab ps L ObjG7.base ((E0 lc).pcOf lc.ctx.f.entry 2) =
      ObjG7.base + BitVec.ofNat 64 (ObjG7.gTab.offs[0]!) := by
    rw [hentry]; exact hpc
  -- the run reaches only `sI`
  have hreach : ∀ b i s, LReach GoFV.Proof.Witness.plRunEnv lc lc.ctx.f.entry 2 sI b i s →
      b = lc.ctx.f.entry ∧ i = 2 ∧ s = sI :=
    fun _ _ _ h => lreach_of_panicAt hb2 hi2 hv6 hpan h
  have hP : RunPre GoFV.Proof.Witness.plRunEnv GenG2.H0 lc GenG7.g L (endP L.text ps.toList)
      (E0 lc) lc.ctx.f.entry 2 sI := by
    intro b i s blk' hr hb'
    obtain ⟨rfl, rfl, rfl⟩ := hreach _ _ _ hr
    rw [hb2] at hb'
    cases hb'
    refine ⟨fun id v hi hv => ?_, fun h => absurd h (by omega)⟩
    rw [hi2] at hi
    cases hi
    rw [hv6] at hv
    cases hv
    have hg : G14Pre lc s (vNil lc) := by
      refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · intro h; rcases h with h | h <;> (rw [hop] at h; cases h)
      · intro _ _ _ hl; rw [hop] at hl; cases hl
      · intro h; rw [hop] at h; cases h
      · intro h; rw [hop] at h; cases h
      · intro _ a x ha hx p hp hnil
        unfold nilArg at hnarg
        rw [ha] at hnarg
        simp only [Option.all_some, hx, hp] at hnarg
        exact absurd (by simpa using hnarg) hnil
      · intro h; rw [hop] at h; cases h
      · intro _ _ _ _ hl; rw [hop] at hl; cases hl
    exact ⟨by rw [hop]; rfl, hg, fun s' hs' => by rw [hpan] at hs'; cases hs'⟩
  have hPP : RunPanicPre GoFV.Proof.Witness.plRunEnv GenG2.H0 lc GenG7.g L (E0 lc)
      lc.ctx.f.entry 2 sI := by
    intro b i s blk' hr hb' id v e mm hi hv _
    obtain ⟨rfl, rfl, rfl⟩ := hreach _ _ _ hr
    rw [hb2] at hb'
    cases hb'
    rw [hi2] at hi
    cases hi
    rw [hv6] at hv
    cases hv
    exact Or.inl hop
  have hent : EntryMatch (E0 lc) sI s0 :=
    { regs := by
        intro r v hv
        by_cases h0 : r = 0
        · subst h0
          rw [(hregs 0 v hv).1 rfl]
          refine ⟨fun q hq => ?_, fun q hq => by simp [objV?] at hq⟩
          simp only [objX?] at hq
          cases hq
          exact ⟨fun h => by rcases h with h | h | h | h <;> exact absurd h (by decide),
            Or.inl (by decide)⟩
        · rw [(hregs r v hv).2 h0]
          exact ⟨fun _ _ => ⟨fun _ => rfl, trivial⟩, fun _ _ => trivial⟩
      flags := hflags
      slots := hslots
      mem := ⟨memI, hmem, memInj⟩ }
  have hinv : G3Inv (E0 lc) lc (kAt lc GenG7.kt lc.ctx.f.entry (blk lc) 2) sI :=
    { core := by
        refine ⟨fun r v c hr hv hcl => ?_, memI, hmem, sep hkeys⟩
        by_cases h0 : r = 0
        · subst h0
          rw [(hregs 0 v hv).1 rfl]
          rw [hk0] at hcl
          cases hcl
          rfl
        · rw [(hregs r v hv).2 h0]; trivial
      slots := by intro k v h; rw [hslots] at h; cases h }
  refine ⟨mm', hrun, ?_⟩
  obtain ⟨e', n, t', he, hn⟩ := obj_whole_panic (H := GenG2.H0) hc hO (hookMap_retLR fun _ => rfl)
    hookPanicMap_H0 (boundsOK_none hnpb) (ObjG7.noICall_spec hni L) hME (by rw [haz]; decide)
    (by decide) (fun _ _ _ h => by rw [Option.isNone_iff_eq_none.1 hchk] at h; cases h)
    (g28Env hc hav hsl hnc hwi hme hend hso) hEE hb2 hbm (by omega) hsI hent hinv hu' hpc hP hPP
    hrun
  rcases he with rfl | ⟨k, x, y, h, -⟩
  · exact ⟨n, t', hn⟩
  · cases h

/-- **A whole function that panics, down to the machine words** (`obj_whole_panic` on `(*A).g`
with a nil receiver): `runLoc`'s run from its first state panics with `nilDeref` at the nil check,
and `runMach` of the linked words from the function's entry panics with `nilDeref`. -/
theorem objWhole_panic_witness :
    ∃ mm', runLoopLoc GoFV.Proof.Witness.plRunEnv GenG7.lc 4
        (locInit GoFV.Proof.Witness.plRunEnv GenG7.lc args {}) GenG7.lc.ctx.f.entry =
        .panicked .nilDeref mm' ∧
      ∃ n t', runMach GenG2.H0 ObjG7.gCode 0x40 n s0 = .panicked .nilDeref t' :=
  panic_of panic_lc_facts

/-! ## `fint64to32`: a static call whose callee panics -/

/-- The callee `runtime.fintto32` panics with `nilDeref`. -/
def envP : Env := { extern := fun _ => some fun _ _ m => .panicked .nilDeref m }

/-- The runtime panics with `nilDeref` at every call. -/
def Hp : Hooks := ⟨fun m => some (.panicked .nilDeref m)⟩

/-- What compiled evaluation checks on `fint64to32`: `checkG30` accepts it with `checkG9`'s
tables, it has no write barrier and no interface or closure call, and the static call `v8` panics
with `nilDeref` from `GenG9.s0 5` in `envP`. -/
def callFacts : Bool :=
  (checkG30 GenG9.lc GenG9.ps GenG9.bs GenG9.g).toOption == some (GenG9.tab, GenG9.kt) &&
    ObjWhole.noWbICall GenG9.lc &&
    isNilPanic (stepLoc envP GenG9.lc (GenG9.s0 5) (GenG9.val 8))

theorem callPanic_facts : callFacts = true := by
  native_decide

/-- `GenG9.g9Env` with no interface or closure call, framed: `G28Env`. -/
theorem g28Env9 (hc : checkG9 GenG9.lc GenG9.ps GenG9.bs GenG9.g = .ok (GenG9.tab, GenG9.kt))
    (hav : (accessedVars GenG9.lc).isEmpty = true) (hsl : (homeSlots GenG9.lc).isEmpty = true)
    (hwi : ObjWhole.noWbICall GenG9.lc = true) :
    G28Env GenG9.lc GenG9.g GenG9.L GenG9.ps 0 GenG9.tab GenG9.E :=
  { env := { env := GenG9.g9Env hc hav hsl
             icalls := fun _ _ _ hv => (ObjWhole.noWbICall_spec hwi hv).2 }
    memeqs := fun h => by cases h }

/-- **A static call whose callee panics** (`g30_callPanic` on `fint64to32`): `runLoc`'s step of
`v8` panics with `nilDeref` (the callee's panic), and from the `LocMatch`ed machine state before it
the P0 Progs run through the `CALL` to the callee's symbol, where `runProg` panics with
`nilDeref` (the hook `Hp`, `CallPanicOK`). -/
theorem g30_callPanic_witness :
    ∃ mm', stepLoc envP GenG9.lc (GenG9.s0 5) (GenG9.val 8) = .panic .nilDeref mm' ∧
      ∃ m', PStar Hp GenG9.L GenG9.ps.toList 0 (GenG9.m0 5) m' ∧
        PPanics Hp GenG9.L GenG9.ps.toList 0 m' .nilDeref := by
  have hf := callPanic_facts
  simp only [callFacts, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨hres, hwi⟩, hpan⟩ := hf
  obtain ⟨mm', hpan⟩ := isNilPanic_spec hpan
  have hc : checkG30 GenG9.lc GenG9.ps GenG9.bs GenG9.g = .ok (GenG9.tab, GenG9.kt) := by
    revert hres; cases checkG30 GenG9.lc GenG9.ps GenG9.bs GenG9.g <;> simp [Except.toOption]
  obtain ⟨hc9, hav, hsl, hm1, hb, hv8, -, -, hi2, -, -, hop8, -, -, -, hk0, -⟩ := GenG9.facts
  refine ⟨mm', hpan, g30_callPanic hc (g28Env9 hc9 hav hsl hwi) hm1 hb hi2 hv8 hop8
    (GenG9.locMatch0 5) (GenG9.g9Inv0 5 hk0) ?_⟩
  intro _ _ _ _ _ _ _ _ _ m₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ⟨m₁, rfl⟩

end GoFV.Proof.Witness.ObjPanic
