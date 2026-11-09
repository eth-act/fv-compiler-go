import GoFV.Proof.Witness.ObjWhole
import GoFV.Proof.Witness.GenG30

/-!
# Non-vacuity witness: a function with no arm64 op down to the machine words (`obj_whole_ret`)

`runtime.gclinkptr.ptr` (`GenG30`: `checkG36` accepts it, a function with no arm64 op that
`runLoc` runs in Phase 1's mode; `checkObj` accepts its assembled words, a frameless leaf without
a stack check):

```go
func (p gclinkptr) ptr() *gclink { return (*gclink)(unsafe.Pointer(p)) }
```

From `runLoc`'s first state on the argument `p = 0x1234` in the Phase 1 test environment
`plRunEnv`, the entry values `v6 = ArgIntReg` (`R0`) and `v1 = InitMem` run to `sI`; the run then
runs `v8 = Convert` (no code), `v10 = MakeResult` and returns `0x1234` at the result's pointer
shape. The machine starts at the function's entry `base` (`MachEntry`: `SP = 0x7fff0000`,
`X0 = 0x1234`, `g = 0x9000`, the caller's `LR = 0x40` outside the code, `R29 = SP - 8`, `p`'s
image at its Phase 1 address). `obj_whole_ret` gives a `runMach` of the linked words that returns
to `0x40` (`MachRet`) with `X0 = 0x1234`, the function's ABI result register (`retRegsOK` and
`ret_results` in Phase 1's mode, `ResultRel`). By compiled evaluation (`native_decide`, listed in
`scripts/axioms-allowlist.txt`; `nl_obj_facts`, `nl_lc_facts`): the validators accept, the run
returns `0x1234`, and the states and tables are as stated.
-/

namespace GoFV.Proof.Witness.ObjWholeNL

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen GoFV.Proof.Obj
open GoFV.Proof (enterListLoc)
open GoFV.Proof.Witness.ObjFrame (isOk getOk eq_getOk)
open GoFV.Proof.Witness.ObjWhole (ι addrAgree isPoison noWbICall noWbICall_spec noMemEq
  noMemEq_spec)

abbrev ps : Array Prog := GenG30.ps

/-- The frameless layout `checkObj`'s frame gives: every symbol at `GenG2.symA`. -/
abbrev L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 0 0 ps.toList

/-- The argument `p = 0x1234`. -/
def args : List Val := [.i64 0x1234]

/-- Block `b1` of `lc`. -/
def blkOf (lc : LocCtx) : Block := (lc.ctx.f.block? 1).getD default

/-- The frame memory: `plRunEnv`'s globals, the outgoing-arguments area, `p`'s image, the result
slot. -/
def memI : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] }),
      (.global "runtime.writeBarrier", { data := #[.b 0, .b 0, .b 0, .b 0], writable := false }),
      (.outargs 0, { data := #[] }),
      (.local 0 3, { data := #[.b 0x34, .b 0x12, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] }),
      (.local 0 4, { data := #[.poison, .poison, .poison, .poison, .poison, .poison, .poison,
        .poison] })] }

/-- The machine memory: `p`'s image (`0x1234`) at its address. -/
def mm : Memory := fun a =>
  if a = ObjWhole.pAddr then 0x34 else if a = ObjWhole.pAddr + 1 then 0x12 else 0

/-- The activation of `runLoc`'s context `lc`: frameless, `SP = 0x7fff0000`, `g = 0x9000`,
`LR = 0x40`, `FP = SP - 8`. -/
def E0 (lc : LocCtx) : MatchEnv :=
  { lc, ι, sp := 0x7fff0000, slot := fun _ => none, g := 0x9000, lr := 0x40,
    fp := 0x7fff0000 - 8, framed := false, pcOf := pcOfTab GenG2.text ps.toList GenG30.tab }

/-- The machine at the function's entry. -/
def s0 : MState :=
  { x := fun k => if k = 0 then 0x1234 else if k = 28 then 0x9000
      else if k = 29 then 0x7fff0000 - 8 else if k = 30 then 0x40 else 0,
    sp := 0x7fff0000, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩, pc := ObjG7.base,
    mem := mm }

/-! ## The assembled words -/

def objIn : Except String (Array Spill × ObjIn) := ObjG7.objOf GenG30.fProg

def spills : Array Spill :=
  match objIn with
  | .ok x => x.1
  | .error _ => #[]

def obj : ObjIn :=
  match objIn with
  | .ok x => x.2
  | .error _ => ⟨ByteArray.empty, #[], #[]⟩

/-- What `checkObj` returns on `gclinkptr.ptr`. -/
def otab : Tab := getOk (checkObj ps spills obj)

/-- The linked code of `gclinkptr.ptr`. -/
def code : Code := getOk (linkCode ObjG7.base (fun _ => GenG2.symA) obj.text obj.relocs.toList)

/-! ## Checks on states -/

def isP : Val → Bool
  | .int .w64 x => x == 0x1234
  | _ => false

/-- `R0` holds the integer `0x1234`, every other register `poison`; no flags, no slot, the frame
memory. -/
def sIIs (s : LocState) : Bool :=
  (List.range s.regs.size).all (fun r =>
      match s.regs[r]? with
      | some v => if r = 0 then isP v else isPoison v
      | none => true) &&
    isPoison s.flags && s.slots.isEmpty &&
    match s.mem with
    | .mem m => decide (m = memI)
    | _ => false

theorem sIIs_spec {s : LocState} (h : sIIs s = true) :
    (∀ r v, s.regs[r]? = some v → (r = 0 → v = .i64 0x1234) ∧ (r ≠ 0 → v = .poison)) ∧
      s.flags = .poison ∧ s.slots = [] ∧ s.mem = .mem memI := by
  simp only [sIIs, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.isEmpty_iff] at h
  obtain ⟨⟨⟨hr, hf⟩, hs⟩, hm⟩ := h
  refine ⟨fun r v hv => ?_, ?_, hs, ?_⟩
  · have hlt := (Array.getElem?_eq_some_iff.1 hv).1
    have := hr r hlt
    rw [hv] at this
    constructor
    · rintro rfl
      simp only [↓reduceIte, isP] at this
      split at this
      · rename_i x
        simp only [beq_iff_eq] at this
        subst this; rfl
      · cases this
    · intro h0
      simp only [h0, ↓reduceIte, isPoison] at this
      split at this
      · rfl
      · cases this
  · unfold isPoison at hf
    split at hf
    · assumption
    · cases hf
  · split at hm
    · simp only [decide_eq_true_eq] at hm
      subst hm; assumption
    · cases hm

/-- The outcome returns the 64-bit integer `0x1234`. -/
def isRetP : Outcome → Bool
  | .returned [.int .w64 x] _ => x == 0x1234
  | _ => false

theorem isRetP_spec {o : Outcome} (h : isRetP o = true) :
    ∃ mm, o = .returned [.int .w64 0x1234] mm := by
  unfold isRetP at h
  split at h
  · simp only [beq_iff_eq] at h
    subst h
    exact ⟨_, rfl⟩
  · cases h

/-- No symbol of `gclinkptr.ptr` is one of `plRunEnv`'s globals. -/
def symsOut : Bool :=
  GenG30.g.syms.all fun x =>
    x.1.toStringLossy != "main.g" && x.1.toStringLossy != "runtime.writeBarrier"

/-- What compiled evaluation checks of the machine side: `checkObj` accepts with no frame and no
stack check, the linked code, no `CALL (Rn)`, the return address `0x40` is no P0 address, the P0
address of the entry's value 2 maps to the body's start, and `memI`'s keys are distinct. -/
def objFacts : Bool :=
  ObjG7.envFacts ps spills obj && otab.check.isNone &&
    ps.toList.all (fun p => addrP GenG2.text p.id != 0x40) &&
    (0x40 : BitVec 64) != endP GenG2.text ps.toList &&
    ObjEnv.map otab ps L ObjG7.base (pcOfTab GenG2.text ps.toList GenG30.tab 1 2) ==
      ObjG7.base + BitVec.ofNat 64 (otab.offs[0]!) &&
    decide ((memI.blocks.toList.map (·.1)).Nodup) && symsOut && ObjG7.noICall ps

theorem nl_obj_facts : objFacts = true := by
  native_decide

/-- What compiled evaluation checks of `runLoc` on `gclinkptr.ptr`: no arm64 op; `checkG36`
accepts it with `GenG30`'s tables and `retRegsOK` its return (the result in `R0`); no frame
variable, home slot, static or indirect call, write barrier or `LoweredMemEq`; the entry is `b1`,
with four values, the first two running from `runLoc`'s first state on `p = 0x1234` to
`R0 = 0x1234` and the frame memory; `R0` has class 64 after them and no upper-bit fact is carried;
simple ops from there on; the whole run returns `0x1234`. -/
def lcFacts (lc : LocCtx) : Bool :=
  !lc.ctx.f.lowered &&
    (checkG36 lc ps GenG30.bs GenG30.g).toOption == some (GenG30.tab, GenG30.kt) &&
    retRegsOK lc GenG30.kt && ownOutRegs lc == [0] &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty && GenG2.noCalls lc && noWbICall lc &&
    lc.ctx.f.entry == 1 && lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    2 ≤ (blkOf lc).values.size &&
    GenG1.okThen (enterListLoc GoFV.Proof.Witness.plRunEnv lc
      (locInit GoFV.Proof.Witness.plRunEnv lc args {}) ((blkOf lc).values.toList.take 2)) sIIs &&
    (kAt lc GenG30.kt 1 (blkOf lc) 2).get 0 == some 64 && simpleFrom lc.ctx.f 1 2 &&
    noMemEq lc && (uL35 lc [] (blkOf lc) 2).isEmpty &&
    isRetP (runLoopLoc GoFV.Proof.Witness.plRunEnv lc 4
      (locInit GoFV.Proof.Witness.plRunEnv lc args {}) lc.ctx.f.entry)

theorem nl_lc_facts : lcFacts GenG30.lc = true := by
  native_decide

/-! ## The activation -/

theorem memInj : MemInj ι memI mm where
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
    · cases ha
      simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
        simp [ByteRel, mm, ObjWhole.pAddr, ObjWhole.gAddr1]
    · cases ha
      simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ => simp [ByteRel, mm, ObjWhole.pAddr, ObjWhole.gAddr2]
    · simp at hi
    · cases ha
      simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
        simp [ByteRel, mm, ObjWhole.pAddr]
    · simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => trivial

theorem sep {lc : LocCtx} (hk : (memI.blocks.toList.map (·.1)).Nodup) :
    KeysNodup memI ∧ SepFrom ι (StkAt (E0 lc)) memI := by
  refine ⟨hk, fun b al a _ _ y hy => ?_⟩
  rcases hy with ⟨h, -⟩ | ⟨k, off, h, -⟩ <;> cases h

theorem g28Env {lc : LocCtx}
    (hc : checkG36 lc ps GenG30.bs GenG30.g = .ok (GenG30.tab, GenG30.kt))
    (hav : (accessedVars lc).isEmpty = true) (hsl : (homeSlots lc).isEmpty = true)
    (hnc : GenG2.noCalls lc = true) (hwi : noWbICall lc = true) (hme : noMemEq lc = true)
    (hend : GenG2.symA ≠ endP GenG2.text ps.toList) (hso : symsOut = true) :
    G28Env lc GenG30.g L ps (endP L.text ps.toList) GenG30.tab (E0 lc) := by
  obtain ⟨-, -, -, -, hlt, -, -⟩ := checkG36_cx hc
  have h2 : G2Env lc GenG30.g L ps 0 GenG30.tab (E0 lc) :=
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
            env := ObjG7.g2Env_endP h2 (ObjG7.retOut_endP hlt) (fun _ => hend)
            vars := by
              intro x hx
              simp [List.isEmpty_iff.1 hav] at hx }
          wbs := fun _ _ _ hv => (noWbICall_spec hwi hv).1 }
        icalls := fun _ _ _ hv => (noWbICall_spec hwi hv).2 }
      memeqs := fun _ _ _ hv => noMemEq_spec hme hv }

/-- **A function with no arm64 op down to the machine words** (`obj_whole_ret` on
`gclinkptr.ptr`, `p = 0x1234`): `runLoc`'s run (in Phase 1's mode) from its first state returns
`0x1234`, and `runMach` of the linked words from the function's entry returns to the caller's
`0x40` (`MachRet`) with `X0 = 0x1234`, the result in the ABI's result register (`ResultRel`). -/
theorem objWholeNL_ret_witness :
    GenG30.lc.ctx.f.lowered = false ∧
    ∃ mm, runLoopLoc GoFV.Proof.Witness.plRunEnv GenG30.lc 4
        (locInit GoFV.Proof.Witness.plRunEnv GenG30.lc args {})
        GenG30.lc.ctx.f.entry = .returned [.int .w64 0x1234] mm ∧
      ∃ E t' n, (E0 GenG30.lc).Extends E ∧ runMach GenG2.H0 code 0x40 n s0 = .returned t' ∧
        MachRet s0 t' ∧ t'.x 0 = 0x1234 ∧ ResultRel E [0] [.int .w64 0x1234] mm t' := by
  -- the machine side
  have hof := nl_obj_facts
  simp only [objFacts, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    decide_eq_true_eq] at hof
  obtain ⟨⟨⟨⟨⟨⟨⟨hef, hchk⟩, hnp⟩, hnend⟩, hpc⟩, hkeys⟩, hso⟩, hni⟩ := hof
  obtain ⟨hO, hend⟩ := ObjG7.envFacts_spec hef
  have hfacts := hef
  simp only [ObjG7.envFacts, Bool.and_eq_true, beq_iff_eq] at hfacts
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, haz⟩, -⟩, -⟩, -⟩, hr40⟩, -⟩, -⟩, -⟩ := hfacts
  replace haz : otab.autosize = 0 := haz
  have hME : MachEntry code ObjG7.base 8 s0 :=
    { pc := rfl, spAlign := by decide, room := by decide, lrOutside := hr40,
      gOutside := by decide, fp := by decide }
  have hEE : EntryEnv (E0 GenG30.lc) L ps.toList otab.autosize s0 :=
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
  have hlf := nl_lc_facts
  simp only [lcFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem,
    Bool.not_eq_true'] at hlf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hres⟩, hrok⟩, houts⟩, hav⟩, hsl⟩, hnc⟩, hwi⟩, hentry⟩, hbm⟩, hbs⟩,
    hsz⟩, hpre⟩, hk0⟩, hsim⟩, hme⟩, hu⟩, hrunP⟩ := hlf
  have hc : checkG36 GenG30.lc ps GenG30.bs GenG30.g = .ok (GenG30.tab, GenG30.kt) := by
    revert hres; cases checkG36 GenG30.lc ps GenG30.bs GenG30.g <;> simp [Except.toOption]
  have hb1 : GenG30.lc.ctx.f.block? 1 = some (blkOf GenG30.lc) := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blkOf, hb]
  obtain ⟨sI, hsI, hsIIs⟩ := GenG1.okThen_spec hpre
  obtain ⟨hregs, hflags, hslots, hmem⟩ := sIIs_spec hsIIs
  obtain ⟨mm, hrun⟩ := isRetP_spec hrunP
  rw [← hentry] at hb1 hk0 hbm
  have hpc' : ObjEnv.map otab ps L ObjG7.base ((E0 GenG30.lc).pcOf GenG30.lc.ctx.f.entry 2) =
      ObjG7.base + BitVec.ofNat 64 (otab.offs[0]!) := by
    rw [hentry]; exact hpc
  have hent : EntryMatch (E0 GenG30.lc) sI s0 :=
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
  have hinv : G3Inv (E0 GenG30.lc) GenG30.lc
      (kAt GenG30.lc GenG30.kt GenG30.lc.ctx.f.entry (blkOf GenG30.lc) 2) sI :=
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
  have hnone := Option.isNone_iff_eq_none.1 hchk
  obtain ⟨E, t', n, hx, hn, hX, hRes⟩ := obj_whole_ret (H := GenG2.H0) hc hO
    (hookMap_retLR fun _ => rfl) (ObjG7.noICall_spec hni L) hrok hME
    (by rw [haz]; decide) (by decide)
    (fun _ _ _ h => by rw [hnone] at h; cases h) (fun _ _ _ h => by rw [hnone] at h; cases h)
    (g28Env hc hav hsl hnc hwi hme hend hso) hEE hb1 hbm (of_decide_eq_true hsz) hsI
    hent (fun _ _ _ h => by rw [hnone] at h; cases h) hinv
    (List.isEmpty_iff.1 hu) hpc' (runPre_simple (by rw [hentry]; exact hsim)) hrun
  rw [houts] at hRes
  have hX0 : t'.x 0 = 0x1234 := by
    rcases (hRes.regs 0 _ 0 rfl rfl).2 with h | ⟨hb, -⟩
    · exact h
    · exact absurd (by decide) hb
  exact ⟨hl, mm, hrun, E, t', n, hx, hn, hX, hX0, hRes⟩

end GoFV.Proof.Witness.ObjWholeNL
