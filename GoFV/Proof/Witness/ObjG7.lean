import GoFV.Proof.Obj.G7
import GoFV.Proof.Witness.ObjFrame
import GoFV.Proof.Witness.GenG7
import GoFV.Proof.Witness.GenG3

/-!
# Non-vacuity witness: slice G7 down to the machine words (`g7_obj_value`, `g7_obj_term`)

Two functions of the corpus that `checkG7` (with the PC and class tables of `GenG7`, `GenG3`) and
`checkObj` both accept, their `.prog` files run through the assembler port as `obj-check` does
(`GoFVTest/ObjCheck.lean`, `checkFile`: `parseProgFile`, `flush`, the port's text, relocations
and final Prog list as the `ObjIn`, the function's spills), with genssa's P0 Progs:

* `(*A).g` of `test/method` (`GenG7`): the nil check `v6` (`MOVB (R0), R27`) on a receiver that
  points to a global (`objG7_value_witness`, `g7_obj_value`);
* `pallocSum.start` of `std/runtime` (`GenG3`): the bit test `TBNZ [63]` of `b1` with bit 63 of
  `x = 7` clear, to `b2` (`objG7_term_witness`, `g7_obj_term`).

Both are frameless leaves (`autosize = 0`), so P0's layout is `GenG7.L`/`GenG3.L` (every symbol at
`GenG2.symA`, the Progs at `0x10000 + 4·ID`). The machine code is linked at `base = 0x20000` with
every symbol at `GenG2.symA`; the caller's return address `retM = 0x40` and the symbols have no
code. P0's return address is `endP` (after the last Prog), which `G6Env` admits by the same facts
(`g2Env_endP`). The callee hook `GenG2.H0` returns through `X30` (`hookMap_retLR`). The machine
starts in the state `relInit` related to the `LocMatch`ed P0 state by the address map (`PC` and
`X30` mapped), here at `base`. By compiled evaluation (`native_decide`, listed in
`scripts/axioms-allowlist.txt`; `g_obj_facts`, `start_obj_facts`): `checkObj` accepts, the frame
is empty, `linkCode` links, the text fits, `retM` and `GenG2.symA` have no code, `GenG2.symA` is
neither a Prog address nor `endP`, and the related machine state's PC is `base`.
-/

namespace GoFV.Proof.Witness.ObjG7

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen GoFV.Proof.Obj
open GoFV.Proof.Witness.ObjFrame (isOk getOk eq_getOk)

/-! ## Common setup -/

/-- The spills and the port's output of a `.prog` file (as `obj-check`). -/
def objOf (prog : String) : Except String (Array Spill × ObjIn) := do
  let pf ← parseProgFile prog.toUTF8
  let out ← flush pf
  return (pf.prog0.fn.spills, { text := out.st.textP, relocs := out.st.textR, progs := out.progs })

/-- Where the machine code is linked. -/
def base : BitVec 64 := 0x20000

/-- The caller's return address. -/
def retM : BitVec 64 := 0x40

/-- The machine state related to `m` by `f`: the PC and `X30` mapped, everything else equal. -/
def relInit (f : BitVec 64 → BitVec 64) (m : MState) : MState :=
  { m with x := fun k => if k = 30 then f (m.x 30) else m.x k, pc := f m.pc }

theorem objRel_relInit (f : BitVec 64 → BitVec 64) (m : MState) : ObjRel f m (relInit f m) where
  x k _ h30 := by
    simp only [relInit]
    split
    · rename_i h; exact absurd h h30
    · rfl
  x30 := by simp [relInit]
  sp := rfl
  v := rfl
  nzcv := rfl
  mem := rfl
  pc := rfl

/-- `endP` is not a Prog address. -/
theorem retOut_endP {sym : Nat → BitVec 64} {text : BitVec 64} {a x : Int} {ps : List Prog}
    (hlt : ∀ p ∈ ps, p.id < 2 ^ 32) :
    ∀ p ∈ ps, (Link.byId sym text a x ps).addr p.id ≠ some (endP text ps) := by
  intro p hp h
  rw [addr_byId hp] at h
  exact not_isProgAddr_end hlt ⟨p, hp, Option.some.inj h⟩

/-- A `G2Env` with return address 0, again with the return address `endP`. -/
theorem g2Env_endP {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog} {tab : PcTab}
    {E : MatchEnv} (h : G2Env lc g L ps 0 tab E)
    (hret : ∀ p ∈ ps.toList, L.addr p.id ≠ some (endP L.text ps.toList))
    (hsym : ∀ y, L.sym y ≠ endP L.text ps.toList) :
    G2Env lc g L ps (endP L.text ps.toList) tab E where
  lcEq := h.lcEq
  link := h.link
  pcOf := h.pcOf
  retOut := hret
  addr := h.addr
  glob := h.glob
  syms y := ⟨hsym y, (h.syms y).2⟩
  calls := h.calls
  slot := h.slot
  extra := h.extra
  frame := h.frame

/-- `ObjEnv` of a frameless function under the ID layout with every symbol at `GenG2.symA`. -/
theorem objEnv_of {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab} {code : Code}
    (hc : checkObj ps spills o = .ok tab) (haz : tab.autosize = 0) (hez : tab.extrasize = 0)
    (hl : linkCode base (fun _ => GenG2.symA) o.text o.relocs.toList = .ok code)
    (hsz : o.text.size ≤ 2 ^ 64) (hret : code retM = none) (hsym : code GenG2.symA = none)
    (hnp : ∀ p ∈ ps.toList, addrP GenG2.text p.id ≠ GenG2.symA)
    (hend : GenG2.symA ≠ endP GenG2.text ps.toList) :
    ObjEnv ps spills o tab (Link.byId (fun _ => GenG2.symA) GenG2.text 0 0 ps.toList) base code
      retM where
  check := hc
  link := by rw [haz, hez]; rfl
  linked := hl
  size := hsz
  ret := hret
  syms _ := ⟨hsym, show GenG2.symA ≠ retM by decide, fun ⟨p, hp, h⟩ => hnp p hp h, hend⟩

/-- The facts `objEnv_of` and `g2Env_endP` need, as one boolean. -/
def envFacts (ps : Array Prog) (spills : Array Spill) (o : ObjIn) : Bool :=
  isOk (checkObj ps spills o) && (getOk (checkObj ps spills o)).autosize == 0 &&
    (getOk (checkObj ps spills o)).extrasize == 0 &&
    isOk (linkCode base (fun _ => GenG2.symA) o.text o.relocs.toList) &&
    decide (o.text.size ≤ 2 ^ 64) &&
    getOk (linkCode base (fun _ => GenG2.symA) o.text o.relocs.toList) retM == none &&
    getOk (linkCode base (fun _ => GenG2.symA) o.text o.relocs.toList) GenG2.symA == none &&
    ps.toList.all (fun p => addrP GenG2.text p.id != GenG2.symA) &&
    GenG2.symA != endP GenG2.text ps.toList

theorem envFacts_spec {ps : Array Prog} {spills : Array Spill} {o : ObjIn}
    (h : envFacts ps spills o = true) :
    ObjEnv ps spills o (getOk (checkObj ps spills o))
        (Link.byId (fun _ => GenG2.symA) GenG2.text 0 0 ps.toList) base
        (getOk (linkCode base (fun _ => GenG2.symA) o.text o.relocs.toList)) retM ∧
      GenG2.symA ≠ endP GenG2.text ps.toList := by
  simp only [envFacts, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc, haz⟩, hez⟩, hl⟩, hsz⟩, hret⟩, hsym⟩, hnp⟩, hend⟩ := h
  exact ⟨objEnv_of (eq_getOk hc) haz hez (eq_getOk hl) hsz hret hsym
    (fun p hp => by simpa using hnp p hp) hend, hend⟩

/-- `G6Env` at `endP` from `G6Env` at 0, for a layout with every symbol at `GenG2.symA`. -/
theorem g6Env_endP {lc : LocCtx} {g : G2In} {ps : Array Prog} {tab : PcTab} {E : MatchEnv}
    (h : G6Env lc g (Link.byId (fun _ => GenG2.symA) GenG2.text 0 0 ps.toList) ps 0 tab E)
    (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hend : GenG2.symA ≠ endP GenG2.text ps.toList) :
    G6Env lc g (Link.byId (fun _ => GenG2.symA) GenG2.text 0 0 ps.toList) ps
      (endP GenG2.text ps.toList) tab E :=
  ⟨g2Env_endP h.env (retOut_endP hlt) (fun _ => hend), h.vars⟩

/-- No `CALL (Rn)` in the list. -/
def noICall (ps : Array Prog) : Bool := ps.toList.all fun p => !isICall p

theorem noICall_spec {ps : Array Prog} (h : noICall ps = true) (L : Link) (s : MState) :
    ICallOut L ps.toList s :=
  iCallOut_of_none (fun p hp => by
    simp only [noICall, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact h p hp) s

/-! ## `(*A).g`: a value -/

def gObjIn : Except String (Array Spill × ObjIn) := objOf GenG7.gProg

def gSpills : Array Spill :=
  match gObjIn with
  | .ok x => x.1
  | .error _ => #[]

def gObj : ObjIn :=
  match gObjIn with
  | .ok x => x.2
  | .error _ => ⟨ByteArray.empty, #[], #[]⟩

/-- What `checkObj` returns on `(*A).g`. -/
def gTab : Tab := getOk (checkObj GenG7.ps gSpills gObj)

/-- The linked code of `(*A).g`. -/
def gCode : Code := getOk (linkCode base (fun _ => GenG2.symA) gObj.text gObj.relocs.toList)

/-- The address map of `(*A).g`. -/
def gMap : BitVec 64 → BitVec 64 := ObjEnv.map gTab GenG7.ps GenG7.L base

/-- The machine state related to `GenG7.m0 GenG2.symA` (before `v6`). -/
def gT0 : MState := relInit gMap (GenG7.m0 GenG2.symA)

/-- What compiled evaluation checks on `(*A).g`: `envFacts`, no `CALL (Rn)`, and the machine
starts at `base`. -/
def gObjFacts : Bool := envFacts GenG7.ps gSpills gObj && noICall GenG7.ps && gT0.pc == base

theorem g_obj_facts : gObjFacts = true := by
  native_decide

/-- **G7 on `(*A).g`, down to the machine words**: when the receiver points to `s`, the nil check
`v6` (`MOVB (R0), R27`) is matched by machine steps of the linked code of `(*A).g` from `gT0`
(at `base`) to a state related to a `LocMatch`ed state before `v11`. -/
theorem objG7_value_witness :
    gT0.pc = base ∧
    ∃ s1 E' m1 t1, stepLoc default GenG7.lc (GenG7.s0 GenG4.ptrS) GenG7.v6 = .ok s1 ∧
      GenG7.E.Extends E' ∧ LocMatch E' s1 2 3 m1 ∧
      G3Inv E' GenG7.lc (kAt GenG7.lc GenG7.kt 2 GenG7.blk2 3) s1 ∧
      MStar GenG2.H0 gCode retM gT0 t1 ∧ ObjRel gMap m1 t1 := by
  have hf := g_obj_facts
  simp only [gObjFacts, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨hef, hni⟩, hpc⟩ := hf
  obtain ⟨hO, hend⟩ := envFacts_spec hef
  obtain ⟨hc, hav, hsl, hnc, hm2, hb, hv, hi2, hop, harg, hk0, hread, hrun, -⟩ := GenG7.facts
  obtain ⟨s1, hs1, -⟩ := GenG1.okThen_spec hrun
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG7_spec hc
  have hE := g6Env_endP (GenG7.g7Env hc hav hsl hnc) hlt hend
  have hpre : G7Pre GenG7.lc (GenG7.s0 GenG4.ptrS) GenG7.v6 := by
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, fun _ a x ha hx p hp _ => ?_⟩
    · intro h
      rcases h with h | h <;> rw [hop] at h <;> cases h
    · intro _ _ _ hl
      rw [hop] at hl
      cases hl
    · intro h
      rw [hop] at h
      cases h
    · intro h
      rw [hop] at h
      cases h
    rw [harg] at ha
    cases ha
    obtain ⟨x', hx', hall⟩ := GenG1.okThen_spec hread
    rw [hx] at hx'
    cases hx'
    rw [hp] at hall
    exact ⟨GenG4.memS, rfl, by simpa using hall⟩
  obtain ⟨E', m1, t1, hx, -, hlm, hinv, hst, hR⟩ := g7_obj_value (H := GenG2.H0) (env := default)
    hc hE hm2 hb hi2 hv (by rw [hop]; rfl)
    (GenG7.locMatch0 GenG4.ptrS GenG2.symA ⟨GenG2.symA, rfl, by decide⟩)
    (GenG7.g7Inv0 _ hk0) hpre (GenG2.callOK_ne (by rw [hop]; nofun)) hs1 hO
    (hookMap_retLR fun _ => rfl) (objRel_relInit _ _) (fun u _ => noICall_spec hni _ u)
  exact ⟨hpc, s1, E', m1, t1, hs1, hx, hlm, hinv, hst, hR⟩

/-! ## `pallocSum.start`: a terminator -/

def startObjIn : Except String (Array Spill × ObjIn) := objOf GenG3.startProg

def startSpills : Array Spill :=
  match startObjIn with
  | .ok x => x.1
  | .error _ => #[]

def startObj : ObjIn :=
  match startObjIn with
  | .ok x => x.2
  | .error _ => ⟨ByteArray.empty, #[], #[]⟩

/-- What `checkObj` returns on `pallocSum.start`. -/
def startTab : Tab := getOk (checkObj GenG3.ps startSpills startObj)

/-- The linked code of `pallocSum.start`. -/
def startCode : Code :=
  getOk (linkCode base (fun _ => GenG2.symA) startObj.text startObj.relocs.toList)

/-- The address map of `pallocSum.start`. -/
def startMap : BitVec 64 → BitVec 64 := ObjEnv.map startTab GenG3.ps GenG3.L base

/-- The machine state related to `GenG3.m0 7` (at `b1`'s terminator). -/
def startT0 : MState := relInit startMap (GenG3.m0 7)

/-- What compiled evaluation checks on `pallocSum.start`: `checkG7` accepts it with `GenG3`'s
tables, it accesses no frame variable, `envFacts`, no `CALL (Rn)`, and the machine starts at
`base`. -/
def startObjFacts : Bool :=
  (checkG7 GenG3.lc GenG3.ps GenG3.bs GenG3.g).toOption == some (GenG3.tab, GenG3.kt) &&
    (accessedVars GenG3.lc).isEmpty && envFacts GenG3.ps startSpills startObj &&
    noICall GenG3.ps && startT0.pc == base

theorem start_obj_facts : startObjFacts = true := by
  native_decide

/-- **G7 on `pallocSum.start`, down to the machine words**: the bit test `TBNZ [63]` of `b1`
(bit 63 of `x = 7` clear) is matched by machine steps of the linked code of `pallocSum.start`
from `startT0` (at `base`) to a state related to a `LocMatch`ed state at the start of `b2`. -/
theorem objG7_term_witness :
    startT0.pc = base ∧
    ∃ s1 e m1 t1, stepTermLoc GenG3.lc (GenG2.s0 7) GenG3.blk1 = .ok (.goto e, s1) ∧ e.b = 2 ∧
      LocMatch GenG3.E s1 2 0 m1 ∧ G3Inv GenG3.E GenG3.lc (GenG3.kt.at 2) s1 ∧
      MStar GenG2.H0 startCode retM startT0 t1 ∧ ObjRel startMap m1 t1 := by
  have hf := start_obj_facts
  simp only [startObjFacts, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨hres7, hnv⟩, hef⟩, hni⟩, hpc⟩ := hf
  obtain ⟨hO, hend⟩ := envFacts_spec hef
  have hc7 : checkG7 GenG3.lc GenG3.ps GenG3.bs GenG3.g = .ok (GenG3.tab, GenG3.kt) := by
    revert hres7; cases checkG7 GenG3.lc GenG3.ps GenG3.bs GenG3.g <;> simp [Except.toOption]
  have hf3 := GenG3.g3_facts
  simp only [Bool.and_eq_true] at hf3
  have hf1 := hf3.1
  simp only [GenG3.startFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hsl⟩, hnc⟩, hm1⟩, -⟩, hb1s⟩, -⟩, -⟩, hsz⟩, hkind⟩,
    -⟩, -⟩, hk0⟩, hrun⟩ := hf1
  have hc3 : checkG3 GenG3.lc GenG3.ps GenG3.bs GenG3.g = .ok (GenG3.tab, GenG3.kt) := by
    revert hres; cases checkG3 GenG3.lc GenG3.ps GenG3.bs GenG3.g <;> simp [Except.toOption]
  have hb1 : GenG3.lc.ctx.f.block? 1 = some GenG3.blk1 := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [GenG3.blk1, hb]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG7_spec hc7
  have hE : G6Env GenG3.lc GenG3.g GenG3.L GenG3.ps (endP GenG2.text GenG3.ps.toList) GenG3.tab
      GenG3.E :=
    g6Env_endP ⟨GenG3.g3Env hc3 hsl hnc, fun x hx => by simp [List.isEmpty_iff.1 hnv] at hx⟩
      hlt hend
  obtain ⟨⟨n, s1⟩, hs1, hrun⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨hgo, -⟩ := hrun
  obtain ⟨e, rfl, het⟩ := GenG1.gotoIs_spec hgo
  obtain ⟨m1, t1, hlm, hinv, -, hst, hR⟩ := g7_obj_term (H := GenG2.H0) hc7 hE hm1 hb1
    (GenG3.locMatch0 7) (GenG3.g3Inv0 7 (by rw [hsz]; exact hk0))
    (fun hz => by rw [hkind] at hz; rcases hz with h | h <;> cases h) hs1 hO
    (hookMap_retLR fun _ => rfl) (objRel_relInit _ _) (fun u _ => noICall_spec hni _ u)
  exact ⟨hpc, s1, e, m1, t1, hs1, het, het ▸ hlm, het ▸ hinv, hst, hR⟩

end GoFV.Proof.Witness.ObjG7
