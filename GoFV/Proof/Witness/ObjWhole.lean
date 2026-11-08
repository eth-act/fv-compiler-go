import GoFV.Proof.Obj.Whole
import GoFV.Proof.Witness.ObjG7
import GoFV.Proof.Witness.Pipeline

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: a whole function down to the machine words (`obj_whole_ret`)

`pallocSum.start` of `std/runtime` (`GenG3`: `checkG12` accepts it with the tables of `checkG3`;
`ObjG7`: `checkObj` accepts its assembled words, a frameless leaf without a stack check):

```go
func (p pallocSum) start() uint {
	if uint64(p)&uint64(1<<63) != 0 {
		return maxPackedValue
	}
	return uint(uint64(p) & (maxPackedValue - 1))
}
```

From `runLoc`'s first state on the argument `p = 7` in the Phase 1 test environment `plRunEnv`
(`locInit`: the frame memory holds the environment's globals `main.g` and `runtime.writeBarrier`,
`p`'s image and the result slot), the entry values `v6 = ArgIntReg` (`R0`) and `v1 = InitMem` run to
`sI`; the run then takes `b1`'s bit test to `b2`, runs `v19 = ANDconst`, `v22 = MakeResult` and
returns `7`. The machine starts at the function's entry `base` (`MachEntry`: `SP = 0x7fff0000`,
`X0 = 7`, `g = 0x9000`, the caller's `LR = 0x40` outside the code, `R29 = SP - 8`, `p`'s image at
its Phase 1 address, the globals' zero bytes at `0x30000000` and `0x30000010`). `obj_whole_ret` gives a `runMach` of the linked words that returns to
`0x40` in a state related to the state before `b2`'s `Ret` (`ExitRel`). Every premise of the run
(`RunPre`) is vacuous for its ops (`runPre_simple`). By compiled evaluation (`native_decide`,
listed in `scripts/axioms-allowlist.txt`; `obj_facts`, `start_facts`): the validators accept, the
run returns, and the states and tables are as stated. The facts on the `runLoc` side are stated of
any context (`lcFacts`, `whole_of`), so that `ObjEndToEnd` uses them for the pipeline's output.
-/

namespace GoFV.Proof.Witness.ObjWhole

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen GoFV.Proof.Obj
open GoFV.Proof (enterListLoc)

abbrev ps : Array Prog := GenG3.ps
abbrev L : Link := GenG3.L

/-- The argument `p = 7`. -/
def args : List Val := [.i64 7]

/-- Block `b1` of `lc`. -/
def blkOf (lc : LocCtx) : Block := (lc.ctx.f.block? 1).getD default

/-- The frame memory: `plRunEnv`'s globals, the outgoing-arguments area, `p`'s image, the result
slot. -/
def memI : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] }),
      (.global "runtime.writeBarrier", { data := #[.b 0, .b 0, .b 0, .b 0], writable := false }),
      (.outargs 0, { data := #[] }),
      (.local 0 3, { data := #[.b 7, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] }),
      (.local 0 4, { data := #[.poison, .poison, .poison, .poison, .poison, .poison, .poison,
        .poison] })] }

/-- Where `main.g` and `runtime.writeBarrier` are linked. -/
def gAddr1 : BitVec 64 := 0x30000000
def gAddr2 : BitVec 64 := 0x30000010

/-- `ι`: the nil block at 0, `plRunEnv`'s globals at `gAddr1`, `gAddr2`, the other globals at their
symbols, every other block at its Phase 1 address. -/
def ι : Blk → Option (BitVec 64)
  | .nil => some 0
  | .global n =>
    if n = "main.g" then some gAddr1 else if n = "runtime.writeBarrier" then some gAddr2
    else some GenG2.symA
  | b => b.base?.map (BitVec.ofNat 64)

/-- The address of `p`'s image: Phase 1's address of `local 0 3`. -/
def pAddr : BitVec 64 := 0x4000000003000000

/-- The machine memory: `p`'s image (7) at its address. -/
def mm : Memory := fun a => if a = pAddr then 7 else 0

/-- The activation of `runLoc`'s context `lc`: frameless, `SP = 0x7fff0000`, `g = 0x9000`,
`LR = 0x40`, `FP = SP - 8`. -/
def E0 (lc : LocCtx) : MatchEnv :=
  { lc, ι, sp := 0x7fff0000, slot := fun _ => none, g := 0x9000, lr := 0x40,
    fp := 0x7fff0000 - 8, framed := false, pcOf := pcOfTab GenG2.text ps.toList GenG3.tab }

/-- The machine at the function's entry. -/
def s0 : MState :=
  { x := fun k => if k = 0 then 7 else if k = 28 then 0x9000 else if k = 29 then 0x7fff0000 - 8
      else if k = 30 then 0x40 else 0,
    sp := 0x7fff0000, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩, pc := ObjG7.base,
    mem := mm }

/-! ## Checks on states -/

def isPoison : Val → Bool
  | .poison => true
  | _ => false

def is7 : Val → Bool
  | .int .w64 x => x == 7
  | _ => false

/-- `R0` holds the integer 7, every other register `poison`; no flags, no slot, the frame
memory. -/
def sIIs (s : LocState) : Bool :=
  s.regs.size == 64 &&
    (List.range s.regs.size).all (fun r =>
      match s.regs[r]? with
      | some v => if r = 0 then is7 v else isPoison v
      | none => true) &&
    isPoison s.flags && s.slots.isEmpty &&
    match s.mem with
    | .mem m => decide (m = memI)
    | _ => false

theorem sIIs_spec {s : LocState} (h : sIIs s = true) :
    (∀ r v, s.regs[r]? = some v → (r = 0 → v = .i64 7) ∧ (r ≠ 0 → v = .poison)) ∧
      s.flags = .poison ∧ s.slots = [] ∧ s.mem = .mem memI := by
  simp only [sIIs, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨-, hr⟩, hf⟩, hs⟩, hm⟩ := h
  refine ⟨fun r v hv => ?_, ?_, hs, ?_⟩
  · have hlt := (Array.getElem?_eq_some_iff.1 hv).1
    have := hr r hlt
    rw [hv] at this
    constructor
    · rintro rfl
      simp only [↓reduceIte, is7] at this
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

def isRet : Outcome → Bool
  | .returned _ _ => true
  | _ => false

theorem isRet_spec {o : Outcome} (h : isRet o = true) : ∃ rs mm, o = .returned rs mm := by
  unfold isRet at h
  split at h
  · exact ⟨_, _, rfl⟩
  · cases h

/-- No write barrier and no interface or closure call. -/
def noWbICall (lc : LocCtx) : Bool :=
  lc.ctx.f.valueTab.all fun
    | some v => v.op != .ARM64LoweredWB && (icallLead v.op).isNone
    | none => true

theorem noWbICall_spec {lc : LocCtx} (h : noWbICall lc = true) {id : ID} {v : Value}
    (hv : lc.ctx.f.value? id = some v) : v.op ≠ .ARM64LoweredWB ∧ icallLead v.op = none := by
  have h1 : lc.ctx.f.valueTab[id]? = some (some v) := by
    have hv' : (lc.ctx.f.valueTab[id]?).join = some v := hv
    cases h : lc.ctx.f.valueTab[id]? with
    | none => rw [h] at hv'; cases hv'
    | some o => rw [h] at hv'; cases o <;> simp_all
  have h2 := (Array.all_eq_true_iff_forall_mem.1 h) _ (Array.mem_of_getElem? h1)
  simpa using h2

/-- No symbol of `pallocSum.start` is one of `plRunEnv`'s globals. -/
def symsOut : Bool :=
  GenG3.g.syms.all fun x => 
    x.1.toStringLossy != "main.g" && x.1.toStringLossy != "runtime.writeBarrier"

/-- What compiled evaluation checks of the machine side: `checkObj` accepts with no frame and no
stack check, the linked code, no `CALL (Rn)`, the return address `0x40` is no P0 address, the P0 address of `v19`
… of the entry's value 2 maps to the body's start, and `memI`'s keys are distinct. -/
def objFacts : Bool :=
  ObjG7.envFacts ps ObjG7.startSpills ObjG7.startObj && ObjG7.startTab.check.isNone &&
    ps.toList.all (fun p => addrP GenG2.text p.id != 0x40) &&
    (0x40 : BitVec 64) != endP GenG2.text ps.toList &&
    ObjEnv.map ObjG7.startTab ps L ObjG7.base (pcOfTab GenG2.text ps.toList GenG3.tab 1 2) ==
      ObjG7.base + BitVec.ofNat 64 (ObjG7.startTab.offs[0]!) &&
    decide ((memI.blocks.toList.map (·.1)).Nodup) && symsOut && ObjG7.noICall ps

theorem obj_facts : objFacts = true := by
  native_decide

/-- What compiled evaluation checks of a `runLoc` context `lc` (`env`): `checkG12` accepts
genssa's Progs of `pallocSum.start` against it; no frame variable, home slot, static or indirect
call or write barrier; the entry is `b1`, with two values, which run from `runLoc`'s first state
on `p = 7` to `R0 = 7` and the frame memory; `R0` has class 64 after them; simple ops from there
on (`simpleFrom`). -/
def lcFacts (env : Env) (lc : LocCtx) : Bool :=
  (checkG12 lc ps GenG3.bs GenG3.g).toOption == some (GenG3.tab, GenG3.kt) &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty && GenG2.noCalls lc && noWbICall lc &&
    lc.ctx.f.entry == 1 && lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (blkOf lc).values.size == 2 &&
    GenG1.okThen (enterListLoc env lc (locInit env lc args {}) ((blkOf lc).values.toList.take 2))
      sIIs &&
    (kAt lc GenG3.kt 1 (blkOf lc) 2).get 0 == some 64 && simpleFrom lc.ctx.f 1 2

/-! ## The activation -/

theorem addrAgree : AddrAgree ι := by
  intro b n a hb ha _
  cases b <;> simp [ι, Blk.base?] at ha hb <;> (try subst hb) <;> (try subst ha) <;> rfl

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
        simp [ByteRel, mm, pAddr, gAddr1]
    · cases ha
      simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ => simp [ByteRel, mm, pAddr, gAddr2]
    · simp at hi
    · cases ha
      simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [ByteRel, mm, pAddr]
    · simp only at hi
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => trivial

theorem sep {lc : LocCtx} (hk : (memI.blocks.toList.map (·.1)).Nodup) :
    KeysNodup memI ∧ SepFrom ι (StkAt (E0 lc)) memI := by
  refine ⟨hk, fun b al a _ _ y hy => ?_⟩
  rcases hy with ⟨h, -⟩ | ⟨k, off, h, -⟩ <;> cases h

theorem g10Env {lc : LocCtx} (hc : checkG12 lc ps GenG3.bs GenG3.g = .ok (GenG3.tab, GenG3.kt))
    (hav : (accessedVars lc).isEmpty = true) (hsl : (homeSlots lc).isEmpty = true)
    (hnc : GenG2.noCalls lc = true) (hwi : noWbICall lc = true)
    (hend : GenG2.symA ≠ endP GenG2.text ps.toList) (hso : symsOut = true) :
    G10Env lc GenG3.g L ps (endP L.text ps.toList) GenG3.tab (E0 lc) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG12_spec hc
  have h2 : G2Env lc GenG3.g L ps 0 GenG3.tab (E0 lc) :=
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
          env := ObjG7.g2Env_endP h2 (ObjG7.retOut_endP hlt) (fun _ => hend)
          vars := by
            intro x hx
            simp [List.isEmpty_iff.1 hav] at hx }
        wbs := fun _ _ _ hv => (noWbICall_spec hwi hv).1 }
      icalls := fun _ _ _ hv => (noWbICall_spec hwi hv).2 }

/-- The machine-side premises of `obj_whole_ret` on `pallocSum.start`. -/
theorem obj_premises :
    ObjEnv ps ObjG7.startSpills ObjG7.startObj ObjG7.startTab L ObjG7.base ObjG7.startCode
      (s0.x 30) ∧
    HookMap GenG2.H0 L ps.toList (ObjEnv.map ObjG7.startTab ps L ObjG7.base) ∧
    MachEntry ObjG7.startCode ObjG7.base 8 s0 ∧ ObjG7.startTab.autosize + 8 ≤ 8 ∧
    (s0.x 28).toNat + 32 ≤ 2 ^ 64 ∧
    (∀ ce tail gOff, ObjG7.startTab.check = some (ce, tail, gOff) →
      CheckPasses ObjG7.startTab.autosize gOff s0) ∧
    (ObjG7.startTab.autosize = 0 ∨ ObjG7.startTab.leaf = false) ∧
    GenG2.symA ≠ endP GenG2.text ps.toList ∧
    (∀ lc, EntryEnv (E0 lc) L ps.toList ObjG7.startTab.autosize s0) ∧
    (∀ lc, ObjEnv.map ObjG7.startTab ps L ObjG7.base ((E0 lc).pcOf 1 2) =
      ObjG7.base + BitVec.ofNat 64 (ObjG7.startTab.offs[0]!)) ∧
    (memI.blocks.toList.map (·.1)).Nodup ∧ symsOut = true ∧ (∀ u, ICallOut L ps.toList u) := by
  have hf := obj_facts
  simp only [objFacts, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨hef, hchk⟩, hnp⟩, hnend⟩, hpc⟩, hkeys⟩, hso⟩, hni⟩ := hf
  obtain ⟨hO, hend⟩ := ObjG7.envFacts_spec hef
  have hfacts := hef
  simp only [ObjG7.envFacts, Bool.and_eq_true, beq_iff_eq] at hfacts
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, haz⟩, -⟩, -⟩, -⟩, hr40⟩, -⟩, -⟩, -⟩ := hfacts
  replace haz : ObjG7.startTab.autosize = 0 := haz
  refine ⟨hO, hookMap_retLR fun _ => rfl,
    { pc := rfl, spAlign := by decide, room := by decide, lrOutside := hr40,
      gOutside := by decide, fp := by decide },
    (by rw [haz]; decide), (by decide),
    (fun _ _ _ h => by rw [Option.isNone_iff_eq_none.1 hchk] at h; cases h),
    Or.inl haz, hend, fun lc => ?_, fun _ => hpc, hkeys, hso, ObjG7.noICall_spec hni L⟩
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

/-- The `runLoc`-side premises of `obj_whole_ret` on `pallocSum.start` in a context `lc` that
meets `lcFacts`. -/
theorem lc_premises {env : Env} {lc : LocCtx} (hf : lcFacts env lc = true) :
    checkG12 lc ps GenG3.bs GenG3.g = .ok (GenG3.tab, GenG3.kt) ∧
    G10Env lc GenG3.g L ps (endP L.text ps.toList) GenG3.tab (E0 lc) ∧
    lc.ctx.f.block? lc.ctx.f.entry = some (blkOf lc) ∧ lc.ctx.f.entry ∈ lc.ctx.f.blocks.toList ∧
    2 ≤ (blkOf lc).values.size ∧ lc.ctx.f.entry = 1 ∧
    ∃ sI, enterListLoc env lc (locInit env lc args {}) ((blkOf lc).values.toList.take 2) = .ok sI ∧
      EntryMatch (E0 lc) sI s0 ∧
      G3Inv (E0 lc) lc (kAt lc GenG3.kt lc.ctx.f.entry (blkOf lc) 2) sI ∧
      RunPre env GenG2.H0 lc GenG3.g L (endP L.text ps.toList) (E0 lc) lc.ctx.f.entry 2 sI := by
  obtain ⟨-, -, -, -, -, -, -, hend, -, -, hkeys, hso, -⟩ := obj_premises
  simp only [lcFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, hav⟩, hsl⟩, hnc⟩, hwi⟩, hentry⟩, hbm⟩, hbs⟩, hsz⟩, hpre⟩, hk0⟩,
    hsim⟩ := hf
  have hc : checkG12 lc ps GenG3.bs GenG3.g = .ok (GenG3.tab, GenG3.kt) := by
    revert hres; cases checkG12 lc ps GenG3.bs GenG3.g <;> simp [Except.toOption]
  have hb1 : lc.ctx.f.block? 1 = some (blkOf lc) := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blkOf, hb]
  obtain ⟨sI, hsI, hsIIs⟩ := GenG1.okThen_spec hpre
  obtain ⟨hregs, hflags, hslots, hmem⟩ := sIIs_spec hsIIs
  rw [← hentry] at hb1 hk0 hbm
  refine ⟨hc, g10Env hc hav hsl hnc hwi hend hso, hb1, hbm, by rw [hsz]; exact Nat.le_refl 2, hentry,
    sI, hsI, ?_, ?_, runPre_simple (by rw [hentry]; exact hsim)⟩
  · exact
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
  · exact
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

/-- **`pallocSum.start` down to the machine words, in any `runLoc` context meeting `lcFacts`**:
a returning run of `runLoc`'s body from its first state on `p = 7` is matched by a `runMach` of
the linked words that returns to the caller's `0x40` (`obj_whole_ret`). -/
theorem whole_of {env : Env} {lc : LocCtx} (hf : lcFacts env lc = true) {fuel : Nat}
    {rs : List Val} {mm : Mem}
    (hrun : runLoopLoc env lc fuel (locInit env lc args {}) lc.ctx.f.entry = .returned rs mm) :
    ∃ E bF blkF sF sF' t' n, (E0 lc).Extends E ∧
      runMach GenG2.H0 ObjG7.startCode 0x40 n s0 = .returned t' ∧ ExitRel E sF s0 t' ∧
      lc.ctx.f.block? bF = some blkF ∧ stepTermLoc lc sF blkF = .ok (.ret rs mm, sF') := by
  obtain ⟨hO, hH, hME, hroom, hg, hpass, hlf, -, hEE, hpc, -, -, hic⟩ := obj_premises
  obtain ⟨hc, hE, hb1, hbm, hk, hentry, sI, hsI, hent, hinv, hP⟩ := lc_premises hf
  rw [← hentry] at hpc
  exact obj_whole_ret hc hO hH hic hME hroom hg hpass hlf hE (hEE lc) hb1 hbm hk hsI hent hinv
    (hpc lc) hP hrun

/-- `lcFacts` of `pallocSum.start` (`GenG3.lc`), and its run from `runLoc`'s first state on
`p = 7` returns (compiled evaluation). -/
theorem start_facts :
    (lcFacts GoFV.Proof.Witness.plRunEnv GenG3.lc &&
      isRet (runLoopLoc GoFV.Proof.Witness.plRunEnv GenG3.lc 4
        (locInit GoFV.Proof.Witness.plRunEnv GenG3.lc args {}) GenG3.lc.ctx.f.entry)) = true := by
  native_decide

/-- **A whole function down to the machine words** (`obj_whole_ret` on `pallocSum.start`,
`p = 7`): `runLoc`'s run from its first state returns, and `runMach` of the linked words from the
function's entry returns to the caller's `0x40` in a state related to the state before the
returning terminator (`ExitRel`: `MachRet`, the registers, the memory). -/
theorem objWhole_ret_witness :
    ∃ rs mm, runLoopLoc GoFV.Proof.Witness.plRunEnv GenG3.lc 4
        (locInit GoFV.Proof.Witness.plRunEnv GenG3.lc args {})
        GenG3.lc.ctx.f.entry = .returned rs mm ∧
      ∃ E bF blkF sF sF' t' n, (E0 GenG3.lc).Extends E ∧
        runMach GenG2.H0 ObjG7.startCode 0x40 n s0 = .returned t' ∧ ExitRel E sF s0 t' ∧
        GenG3.lc.ctx.f.block? bF = some blkF ∧
        stepTermLoc GenG3.lc sF blkF = .ok (.ret rs mm, sF') := by
  have hf := start_facts
  simp only [Bool.and_eq_true] at hf
  obtain ⟨rs, mm, hrun⟩ := isRet_spec hf.2
  exact ⟨rs, mm, hrun, whole_of hf.1 hrun⟩

end GoFV.Proof.Witness.ObjWhole
