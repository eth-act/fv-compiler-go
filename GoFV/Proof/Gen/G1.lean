import GoFV.Proof.Gen.Basic
import GoFV.Proof.Gen.Branch
import GoFV.Proof.Gen.Mem
import GoFV.Proof.Gen.Spec
import GoFV.Proof.Gen.Step

/-!
# Soundness of the genssa validator's slice G1 (`docs/plans/proofs3.md` §3)

`g1_value`: when `checkG1` accepts a function, every value of a block (other than the entry
values) run by `runLoc` from a state related by `LocMatch` to a machine state is matched by
`runProg` steps of genssa's P0 Progs (laid out by `Link.byId`) to a state related before the next
value. `g1_term`: a terminator that goes to a successor is matched by steps to a state related
before the successor's first value.

The activation (`G1Env`): the PC of value `i` of block `b` is the address of the Prog at index
`tab[b][i]` (`pcOfTab`), `ret` is no Prog's address, `ι` puts every block with a Phase 1 address
but the frame temporaries there (`AddrAgree`), and the function has no frame. The invariant
(`G1Inv`): no stack slot, every register holds a value of its width class, the memory's block keys
are distinct. The per-step premises (`G1Pre`, `G1TermPre`): the arguments of a compare and the
control of a register test are not pointers without an integer form, a load reads 8 valid bytes,
and the pointer operands of a subtraction are in one block or in no frame temporaries (`SubPre`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## The PC table -/

/-- The address of the Prog at index `j` of `ps` under `Link.byId` (past the end: the fall-through
of the last Prog). -/
def pcAt (text : BitVec 64) (ps : List Prog) (j : Nat) : BitVec 64 :=
  text + BitVec.ofNat 64 (4 * if h : j < ps.length then ps[j].id else maxId ps + 1)

/-- `MatchEnv.pcOf` from `checkG1`'s table: the address of the first Prog of value `i` of block
`b` (`i` = the number of values: of the terminator). -/
def pcOfTab (text : BitVec 64) (ps : List Prog) (tab : PcTab) (b : ID) (i : Nat) : BitVec 64 :=
  pcAt text ps (((tab.lookup b).getD []).getD i 0)

/-! ## The premises -/

/-- The activation of a function `checkG1` accepted with table `tab`. -/
structure G1Env (lc : LocCtx) (L : Link) (ps : Array Prog) (ret : BitVec 64) (tab : PcTab)
    (E : MatchEnv) : Prop where
  lc : E.lc = lc
  link : L = Link.byId L.sym L.text L.autosize L.extrasize ps.toList
  pcOf : E.pcOf = pcOfTab L.text ps.toList tab
  ret : ∀ p ∈ ps.toList, L.addr p.id ≠ some ret
  addr : AddrAgree E.ι
  leaf : E.framed = false

/-- The invariant of G1's `runLoc` states. -/
structure G1Inv (lc : LocCtx) (s : LocState) : Prop where
  slots : s.slots = []
  regs : ∀ r v c, r ≠ zeroReg → s.regs[r]? = some v → regCls lc r = some c → Fits c v
  mem : ∃ mm, s.mem = .mem mm ∧ KeysNodup mm

/-- The addresses `P` lie outside the windows of the live blocks of `mm` under `ι`. -/
def SepFrom (ι : Blk → Option (BitVec 64)) (P : BitVec 64 → Prop) (mm : Mem) : Prop :=
  ∀ b al a, (b, al) ∈ mm.blocks → ι b = some a → ∀ y : BitVec 64, P y →
    ¬ (a.toNat ≤ y.toNat ∧ y.toNat < a.toNat + al.data.size)

/-- The invariant the value steps of every slice keep: every register other than `ZERO` holds a
value of the class the class map `K` gives it (G1, G2: `regCls`, one class per register; G3: the
class of its last writer, by dataflow), the memory's block keys are distinct, and the live blocks
lie away from the addresses `P` (G1: none; G2: the saved `LR`/`FP` words and the spill slots). -/
structure CoreInv (ι : Blk → Option (BitVec 64)) (P : BitVec 64 → Prop) (K : Nat → Option Nat)
    (s : LocState) : Prop where
  regs : ∀ r v c, r ≠ zeroReg → s.regs[r]? = some v → K r = some c → Fits c v
  mem : ∃ mm, s.mem = .mem mm ∧ KeysNodup mm ∧ SepFrom ι P mm

/-- The class map `K'` claims no class `K` does not (outside `ZERO`). -/
def KLe (K' K : Nat → Option Nat) : Prop := ∀ r c, r ≠ zeroReg → K' r = some c → K r = some c

/-- The class map `K` with register `r` set to `c`. -/
def kSet (K : Nat → Option Nat) (r : Nat) (c : Option Nat) : Nat → Option Nat :=
  fun r' => if r' = r then c else K r'

/-- The registers `v` reads (its register arguments; a `Phi` reads none) hold their classes. -/
def KRead (lc : LocCtx) (v : Value) (K : Nat → Option Nat) : Prop :=
  v.op ≠ .Phi → ∀ a ∈ v.args.toList, ∀ r c, lc.home a = some (.reg r) → r ≠ zeroReg →
    cls (lc.ty a) = some c → K r = some c

/-- `K'` follows `K` across a value `v` that writes at most its register home: it claims the
value's class for that register and `K`'s elsewhere (a `Phi` writes nothing). -/
def KNext (lc : LocCtx) (v : Value) (K K' : Nat → Option Nat) : Prop :=
  ∀ r c, r ≠ zeroReg → K' r = some c →
    if v.op ≠ .Phi ∧ lc.home v.id = some (.reg r) then cls (lc.ty v.id) = some c else K r = some c

/-- A machine memory that agrees with `m`'s at the addresses `P` keeps `LocMatch`'s slots and
frame (G1: no slot, no saved words; G2: they lie in `P`). -/
def Keeps (E : MatchEnv) (P : BitVec 64 → Prop) (s : LocState) (m : MState) : Prop :=
  ∀ M : Memory, (∀ y, P y → M y = m.mem y) →
    (∀ k v, s.slots.lookup k = some v → ∃ off, E.slot k = some off ∧
      SlotRel E.ι (E.lc.slotTy k) v M (E.sp + BitVec.ofInt 64 off)) ∧
    FrameRel E { m with mem := M }

/-- A register content that is not a pointer without an integer form. -/
def NoBarePtr (x : Val) : Prop := ∀ p, x = .ptr p → (Arm64.ptrReg p).isSome = true

/-- A subtraction's pointer operands are in one block or in no frame temporaries (`SubOK`). -/
def SubPre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  v.op = .ARM64SUB → ∀ a b x y, v.args[0]? = some a → v.args[1]? = some b →
    s.read lc a = .ok x → s.read lc b = .ok y → SubOK x y

/-- The per-value premises: compare arguments are not pointers without an integer form, a load
reads 8 valid bytes, the pointer operands of a subtraction are in one block or in no frame
temporaries (`SubOK`). -/
def G1Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  ((v.op = .ARM64CMP ∨ v.op = .ARM64CMPconst) →
    ∀ a ∈ v.args.toList, ∀ x, s.read lc a = .ok x → NoBarePtr x) ∧
  (v.op = .ARM64MOVDload → ∀ a x, v.args[0]? = some a → s.read lc a = .ok x →
    ∃ p mm bs, Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p ∧ s.mem = .mem mm ∧
      mm.read p 8 = some bs) ∧
  SubPre lc s v

/-- The per-terminator premise: the control of a register test is not a pointer without an
integer form. -/
def G1TermPre (lc : LocCtx) (s : LocState) (blk : Block) : Prop :=
  (blk.kind = .ARM64Z ∨ blk.kind = .ARM64NZ) →
    ∀ c x, blk.controls[0]? = some c → s.read lc c = .ok x → NoBarePtr x

/-! ## Steps on the ID layout -/

section Steps

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {ps : List Prog}
  {ret : BitVec 64}

theorem addr_pcAt {j : Nat} (hj : j < ps.length) :
    (Link.byId sym text az ez ps).addr ps[j].id = some (pcAt text ps j) := by
  rw [addr_byId (List.getElem_mem hj)]
  simp [pcAt, hj]

theorem nextAddr_pcAt (hnd : (ps.map (·.id)).Nodup) {j : Nat} (hj : j < ps.length) :
    (Link.byId sym text az ez ps).nextAddr ps[j].id = some (pcAt text ps (j + 1)) := by
  rw [nextAddr_byId hnd hj]
  by_cases h : j + 1 < ps.length <;> simp [pcAt, h]

theorem progAt?_pcAt (hnd : (ps.map (·.id)).Nodup) (hlt : ∀ p ∈ ps, p.id < 2 ^ 32) {j : Nat}
    (hj : j < ps.length) :
    progAt? (Link.byId sym text az ez ps) ps (pcAt text ps j) = some ps[j] := by
  have := progAt?_byId (sym := sym) (text := text) (a := az) (x := ez) hnd hlt hj
  simpa [pcAt, hj] using this

/-- The Prog at index `j` executed from its address. -/
theorem pstep_at (hnd : (ps.map (·.id)).Nodup) (hlt : ∀ p ∈ ps, p.id < 2 ^ 32)
    (hret : ∀ p ∈ ps, (Link.byId sym text az ez ps).addr p.id ≠ some ret) {j : Nat}
    (hj : j < ps.length) {m m' : MState} (hpc : m.pc = pcAt text ps j)
    (hs : progStep (Link.byId sym text az ez ps) ps[j] m = .ok m') :
    PStep H (Link.byId sym text az ez ps) ps ret m m' :=
  .prog (fun h => hret _ (List.getElem_mem hj) (by rw [addr_pcAt hj, ← hpc, h]))
    (by rw [hpc]; exact progAt?_pcAt hnd hlt hj) hs

/-- No-ops from index `j` to index `k`. -/
theorem pstar_noops (hnd : (ps.map (·.id)).Nodup) (hlt : ∀ p ∈ ps, p.id < 2 ^ 32)
    (hret : ∀ p ∈ ps, (Link.byId sym text az ez ps).addr p.id ≠ some ret) {j k : Nat}
    (hjk : j ≤ k) (hk : k ≤ ps.length)
    (hno : ∀ l (hl : l < ps.length), j ≤ l → l < k → noop ps[l] = true) (m : MState) :
    PStar H (Link.byId sym text az ez ps) ps ret { m with pc := pcAt text ps j }
      { m with pc := pcAt text ps k } := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  induction d with
  | zero => exact .refl
  | succ d ih =>
    have hk' : j + d < ps.length := by omega
    refine .tail (ih (by omega) (by omega) (fun l hl h1 h2 => hno l hl h1 (by omega))) ?_
    exact pstep_at hnd hlt hret hk' rfl
      (progStep_noop (nextAddr_pcAt hnd hk') (hno (j + d) hk' (by omega) (by omega)))

/-- `OneAt` on the list: no-ops from `j` up to the Prog at `k` of shape `sh`, `j' = k + 1`. -/
theorem pstar_oneAt (hnd : (ps.map (·.id)).Nodup) (hlt : ∀ p ∈ ps, p.id < 2 ^ 32)
    (hret : ∀ p ∈ ps, (Link.byId sym text az ez ps).addr p.id ≠ some ret) {psA : Array Prog}
    (hps : psA.toList = ps) {j j' : Nat} {sh : Shape} (h : OneAt psA j sh j') (m : MState) :
    ∃ k, j' = k + 1 ∧ ∃ hk : k < ps.length, sh.ok ps[k] = true ∧
      PStar H (Link.byId sym text az ez ps) ps ret { m with pc := pcAt text ps j }
        { m with pc := pcAt text ps k } := by
  subst hps
  obtain ⟨k, hjk, rfl, hk, hok, hno⟩ := h
  refine ⟨k, rfl, by simpa using hk, by simpa using hok, ?_⟩
  exact pstar_noops hnd hlt hret hjk (by simp; omega)
    (fun l hl h1 h2 => by simpa using hno l (by simpa using hl) h1 h2) m

end Steps

/-! ## Relations -/

theorem Shape.ok_eq {sh : Shape} {p : Prog} (h : sh.ok p = true) :
    p.as = sh.as ∧ p.from_ = sh.from_ ∧ p.reg = sh.reg ∧ p.to = sh.to ∧ p.scond = 0 := by
  simp only [Shape.ok, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩

theorem wX_pc {m : MState} {q : BitVec 64} {r : Reg} {val : BitVec 64} :
    ({ m with pc := q } : MState).wX r val = { m.wX r val with pc := q } := by
  unfold MState.wX; split <;> rfl

theorem wX_rX_self {m : MState} {r : Reg} : m.wX r (m.rX r) = m := by
  by_cases h : r = 31
  · simp [MState.wX, h]
  · simp only [MState.wX, MState.rX, h, ↓reduceIte]
    cases m
    congr 1
    funext i
    split <;> simp_all

theorem rX_31 {m : MState} : m.rX (BitVec.ofNat 5 31) = 0 := by
  simp [MState.rX]

theorem rX_lt {m : MState} {k : Nat} (hk : k < 31) : m.rX (BitVec.ofNat 5 k) = m.x (BitVec.ofNat 5 k) := by
  have : (BitVec.ofNat 5 k : Reg) ≠ 31 := by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega
  rw [MState.rX, ite_eq_right_iff.2 (fun h => absurd h this)]

variable {E : MatchEnv} {lc : LocCtx} {s : LocState} {b : ID} {i : Nat} {m : MState}

theorem locMatch_pc (h : LocMatch E s b i m) {b' : ID} {i' : Nat} (hpc : E.pcOf b' i' = m.pc) :
    LocMatch E s b' i' m :=
  { h with pc := hpc.symm }

theorem locMatch_setFlags (h : LocMatch E s b i m) {f : Val} {nz : Flags} (hf : FlagsRel f nz)
    {b' : ID} {i' : Nat} :
    LocMatch E { s with flags := f } b' i' { m with nzcv := nz, pc := E.pcOf b' i' } where
  regs := h.regs
  flags := hf
  slots := h.slots
  mem := h.mem
  frame := h.frame
  pc := rfl

/-- A new memory: `runLoc`'s injected into the machine's, with the slots and the frame kept. -/
theorem locMatch_setMem (h : LocMatch E s b i m) {mm' : Mem} {M : Memory}
    (hsl : ∀ k v, s.slots.lookup k = some v → ∃ off, E.slot k = some off ∧
      SlotRel E.ι (E.lc.slotTy k) v M (E.sp + BitVec.ofInt 64 off))
    (hfr : FrameRel E { m with mem := M }) (hM : MemInj E.ι mm' M) {b' : ID} {i' : Nat} :
    LocMatch E { s with mem := .mem mm' } b' i' { m with mem := M, pc := E.pcOf b' i' } where
  regs := h.regs
  flags := h.flags
  slots := hsl
  mem := ⟨mm', rfl, hM⟩
  frame := hfr
  pc := rfl

theorem locMatch_frState {fr : GoFV.SSA.Sem.Frame} (h : LocMatch E s b i m) {b' : ID} {i' : Nat}
    (hpc : E.pcOf b' i' = m.pc) : LocMatch E { s with fr } b' i' m :=
  { h with pc := hpc.symm }

theorem regCls_of_home {vid r c : Nat} (hhome : homeOK lc vid = true)
    (hh : lc.home vid = some (.reg r)) (hrz : r ≠ zeroReg) (hc : cls (lc.ty vid) = some c) :
    regCls lc r = some c := by
  simp only [homeOK, hh] at hhome
  simp [hrz, hc] at hhome
  exact hhome.symm

variable {ι : Blk → Option (BitVec 64)} {P : BitVec 64 → Prop} {K K' : Nat → Option Nat}

theorem G1Inv.core (hinv : G1Inv lc s) : CoreInv ι (fun _ => False) (regCls lc) s := by
  obtain ⟨mm, hmm, hk⟩ := hinv.mem
  exact ⟨hinv.regs, mm, hmm, hk, fun _ _ _ _ _ _ h => h.elim⟩

theorem G1Inv.of_core (hinv : CoreInv ι P (regCls lc) s) (hsl : s.slots = []) : G1Inv lc s := by
  obtain ⟨mm, hmm, hk, -⟩ := hinv.mem
  exact ⟨hsl, hinv.regs, mm, hmm, hk⟩

theorem CoreInv.mono (hinv : CoreInv ι P K s) (h : KLe K' K) : CoreInv ι P K' s :=
  ⟨fun r v c hr hv hc => hinv.regs r v c hr hv (h r c hr hc), hinv.mem⟩

theorem core_setReg (hinv : CoreInv ι P K s) {r c : Nat} {x : Val} (hx : Fits c x) :
    CoreInv ι P (kSet K r (some c)) (s.setReg r x) where
  mem := hinv.mem
  regs := by
    intro r' v c' hr' hv hcls
    simp only [LocState.setReg] at hv
    by_cases hrr : r' = r
    · subst hrr
      simp only [kSet, ↓reduceIte, Option.some.injEq] at hcls
      subst hcls
      split at hv
      · rename_i hlt
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hlt
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt.1] at hv
        cases hv; exact hx
      · rename_i hlt
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_and,
          Decidable.not_not] at hlt
        exact absurd (hlt (Array.getElem?_eq_some_iff.1 hv).1) hr'
    · simp only [kSet, hrr, ↓reduceIte] at hcls
      split at hv
      · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hrr)] at hv
        exact hinv.regs r' v c' hr' hv hcls
      · exact hinv.regs r' v c' hr' hv hcls

theorem core_setFlags (hinv : CoreInv ι P K s) {f : Val} : CoreInv ι P K { s with flags := f } :=
  ⟨hinv.regs, hinv.mem⟩

theorem core_fr (hinv : CoreInv ι P K s) {fr : GoFV.SSA.Sem.Frame} : CoreInv ι P K { s with fr } :=
  ⟨hinv.regs, hinv.mem⟩

/-- `KNext` across a value that writes no register keeps the claims of `K`. -/
theorem knext_same {v : Value} (hK : KNext lc v K K')
    (h : v.op = .Phi ∨ ∀ r, r ≠ zeroReg → lc.home v.id ≠ some (.reg r)) : KLe K' K := by
  intro r c hr hc
  have := hK r c hr hc
  rcases h with h | h
  · simpa [h] using this
  · simpa [h r hr] using this

/-- `KNext` across a value that writes its register home `r` with its class `c`. -/
theorem knext_set {v : Value} (hK : KNext lc v K K') (hop : v.op ≠ .Phi) {r c : Nat}
    (hh : lc.home v.id = some (.reg r)) (hc : cls (lc.ty v.id) = some c) :
    KLe K' (kSet K r (some c)) := by
  intro r' c' hr' hc'
  have := hK r' c' hr' hc'
  by_cases hrr : r' = r
  · subst hrr
    simp only [hop, hh, ne_eq, not_false_eq_true, and_self, ↓reduceIte, hc,
      Option.some.injEq] at this
    simp [kSet, this]
  · have hne : lc.home v.id ≠ some (.reg r') := by rw [hh]; simpa using Ne.symm hrr
    simp only [hne, and_false, ↓reduceIte] at this
    simp [kSet, hrr, this]

/-- A register home G1 handles (`homeOK`) other than `ZERO` holds a value with a class. -/
theorem clsReg_of_home (hhome : ∀ i r, lc.home i = some (.reg r) → homeOK lc i = true) :
    ∀ i r, lc.home i = some (.reg r) → r ≠ zeroReg → (cls (lc.ty i)).isSome = true := by
  intro i r hh hr
  have := hhome i r hh
  simp only [homeOK, hh, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, hr, false_or] at this
  exact this.1

/-- G1's and G2's class map (`regCls`, one class per register) gives each read register its
class. -/
theorem kread_regCls (hhome : ∀ i r, lc.home i = some (.reg r) → homeOK lc i = true) {v : Value} :
    KRead lc v (regCls lc) :=
  fun _ a _ r c hh hr hc => regCls_of_home (hhome a r hh) hh hr hc

/-- G1's and G2's class map follows itself across any value. -/
theorem knext_regCls (hhome : ∀ i r, lc.home i = some (.reg r) → homeOK lc i = true) {v : Value} :
    KNext lc v (regCls lc) (regCls lc) := by
  intro r c hr hc
  split
  · rename_i h
    have hho := hhome _ _ h.2
    cases hcl : cls (lc.ty v.id) with
    | none => simp [homeOK, h.2, hr, hcl] at hho
    | some c' =>
      have := regCls_of_home hho h.2 hr hcl
      rw [hc] at this
      exact this.symm
  · exact hc

theorem retypeL_poison (t : Ty) : Val.retypeL t .poison = .poison := by
  cases t <;> rfl

/-- A register argument read at its shape: related to its machine register and of its class. -/
theorem arg_rel (hA : AddrAgree E.ι) (hl : lc.ctx.f.lowered = true)
    (hm : LocMatch E s b i m) (hinv : CoreInv ι P K s) {a r c k : Nat}
    (hh : lc.home a = some (.reg r)) (hc : cls (lc.ty a) = some c)
    (hK : r ≠ zeroReg → K r = some c)
    (hk : (r = zeroReg ∧ k = 31) ∨ (k < 31 ∧ objX? r = some (BitVec.ofNat 5 k))) :
    ∃ x, s.read lc a = .ok x ∧ ValRel E.ι x (m.rX (BitVec.ofNat 5 k)) ∧ Fits c x := by
  refine ⟨_, read_reg hl hh hc, ?_, fits_retypeL hc _⟩
  rcases hk with ⟨rfl, rfl⟩ | ⟨hk, hobj⟩
  · rw [rX_31]
    simp only [LocState.reg, beq_self_eq_true, ↓reduceIte]
    exact valRel_retypeL hA hc (fits_retypeL hc _) (valRel_zero hc)
  · rw [rX_lt hk]
    have hrz : r ≠ zeroReg := by
      intro h; subst h; simp [objX?, zeroReg] at hobj
    simp only [LocState.reg, beq_iff_eq, hrz, ↓reduceIte]
    cases hv : s.regs[r]? with
    | none => simp only [Option.getD_none, retypeL_poison]; trivial
    | some v =>
      simp only [Option.getD_some]
      exact valRel_retypeL hA hc (hinv.regs r v c hrz hv (hK hrz)) ((hm.regs r v hv).1 _ hobj)

/-- Writing a register G1 may write with a value related to the machine's new word: `LocMatch`
at the next value and the invariant with the register at the value's class. -/
theorem finish_reg (hm : LocMatch E s b i m) (hinv : CoreInv ι P K s) {r c k : Nat} {x : Val}
    {val : BitVec 64} (hd : destOK r = true) (hk : k < 32)
    (hrk : objOf? r = some (GoFV.Asm.ARM64.REG_R0 + k)) (hx : ValRel E.ι x val) (hfx : Fits c x)
    {b' : ID} {i' : Nat} :
    LocMatch E (s.setReg r x) b' i' { m.wX (BitVec.ofNat 5 k) val with pc := E.pcOf b' i' } ∧
      CoreInv ι P (kSet K r (some c)) (s.setReg r x) :=
  ⟨locMatch_setReg hm hk hrk hd hx, core_setReg hinv hfx⟩

/-! ## Small facts -/

theorem arr1 {α : Type} {xs : Array α} {a : α} (h : xs.size = 1) (h0 : xs[0]? = some a) :
    xs = #[a] := by
  rcases xs with ⟨_ | ⟨x, _ | ⟨y, l⟩⟩⟩ <;> simp_all

theorem arr2 {α : Type} {xs : Array α} {a b : α} (h : xs.size = 2) (h0 : xs[0]? = some a)
    (h1 : xs[1]? = some b) : xs = #[a, b] := by
  rcases xs with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩⟩ <;> simp_all

theorem arr3 {α : Type} {xs : Array α} {a b c : α} (h : xs.size = 3) (h0 : xs[0]? = some a)
    (h1 : xs[1]? = some b) (h2 : xs[2]? = some c) : xs = #[a, b, c] := by
  rcases xs with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, l⟩⟩⟩⟩⟩ <;> simp_all

theorem mapM_loop_res {α β : Type} (f : α → Res β) :
    ∀ (l : List α) (acc ys : List β), List.mapM.loop f l acc = .ok ys →
      ∃ zs, ys = acc.reverse ++ zs ∧ zs.length = l.length ∧
        ∀ k (hk : k < l.length) (hz : k < zs.length), f l[k] = .ok zs[k]
  | [], acc, ys, h => by
    simp only [List.mapM.loop] at h
    cases h
    exact ⟨[], by simp, rfl, fun k hk => absurd hk (by simp)⟩
  | a :: l, acc, ys, h => by
    simp only [List.mapM.loop] at h
    cases hfa : f a with
    | ok x =>
      rw [hfa] at h
      obtain ⟨zs, rfl, hlen, hz⟩ := mapM_loop_res f l (x :: acc) ys h
      refine ⟨x :: zs, by simp, by simp [hlen], fun k hk hz' => ?_⟩
      cases k with
      | zero => simpa using hfa
      | succ k => simpa using hz k (by simpa using hk) (by simpa using hz')
    | panic e m => rw [hfa] at h; cases h
    | stuck msg => rw [hfa] at h; cases h

/-- A successful `mapM` in `Res`: one result per element. -/
theorem mapM_res {α β : Type} {f : α → Res β} {l : List α} {ys : List β}
    (h : l.mapM f = .ok ys) :
    ys.length = l.length ∧ ∀ k (hk : k < l.length) (hy : k < ys.length), f l[k] = .ok ys[k] := by
  obtain ⟨zs, rfl, hlen, hz⟩ := mapM_loop_res f l [] ys h
  exact ⟨by simpa using hlen, fun k hk hy => by simpa using hz k hk (by simpa using hy)⟩

theorem mapM_res_two {α β : Type} {f : α → Res β} {a b : α} {x y : β} {ys : List β}
    (h : [a, b].mapM f = .ok ys) (hx : f a = .ok x) (hy : f b = .ok y) : ys = [x, y] := by
  obtain ⟨hlen, hk⟩ := mapM_res h
  match ys, hlen with
  | [x', y'], _ =>
    have h0 := hk 0 (by simp) (by simp)
    have h1 := hk 1 (by simp) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, hx, hy, Res.ok.injEq] at h0 h1
    rw [h0, h1]

theorem mapM_res_one {α β : Type} {f : α → Res β} {a : α} {x : β} {ys : List β}
    (h : [a].mapM f = .ok ys) (hx : f a = .ok x) : ys = [x] := by
  obtain ⟨hlen, hk⟩ := mapM_res h
  match ys, hlen with
  | [x'], _ =>
    have h0 := hk 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero, hx, Res.ok.injEq] at h0
    rw [h0]

theorem objOf?_inj {r r' : Nat} {o : Int} (h : objOf? r = some o) (h' : objOf? r' = some o) :
    r = r' := by
  obtain ⟨k, hk, rfl, hr⟩ := objOf?_some h
  obtain ⟨k', hk', he, hr'⟩ := objOf?_some h'
  have hkk : k = k' := by omega
  subst hkk
  rcases hr with ⟨rfl, rfl⟩ | ⟨hk1, hx⟩ <;> rcases hr' with ⟨rfl, h2⟩ | ⟨hk2, hx'⟩
  · rfl
  · omega
  · omega
  · exact objX?_inj hx hx'

theorem isFlags_eq {t : Ty} (h : t.isFlags = true) : t = Ty.flags := by
  unfold Ty.isFlags at h
  split at h
  · rfl
  · cases h

theorem memTy_eq {t : Ty} (h : memTy t = true) : t = .mem := by
  cases t <;> simp_all [memTy]

theorem cls_le {t : Ty} {c : Nat} (h : cls t = some c) : c ≤ 64 := by
  cases t with
  | int w => simp only [Gen.Check.cls, Option.some.injEq] at h; subst h; cases w <;> decide
  | ptr _ => simp only [Gen.Check.cls, Option.some.injEq] at h; omega
  | bool => simp only [Gen.Check.cls, Option.some.injEq] at h; omega
  | _ => simp [Gen.Check.cls] at h

theorem cls_ne_bool {t : Ty} {c : Nat} (h : cls t = some c) (h8 : 8 ≤ c) : t ≠ .bool := by
  rintro rfl; simp [Gen.Check.cls] at h; omega

theorem loadN_eq {t : Ty} (ht : t ≠ .bool) {mm : Mem} {p : Ptr} :
    Arm64.loadN t 8 false mm p = mm.load (.int .w64) p := by
  simp only [Arm64.loadN]
  split
  · rename_i x hx
    rw [hx]
    cases t <;> first | rfl | exact absurd rfl ht
  · rfl

theorem storeBytes_size8 (x : Val) : (Arm64.storeBytes 8 x).size = 8 := by
  unfold Arm64.storeBytes
  split
  · simp [ptrBytes]
  · split <;> simp_all
  · split
    · simp [intBytes]
    · simp

theorem canWrite_of_write {mm mm' : Mem} {p : Ptr} {bs : Array Byte} (h : mm.write p bs = some mm')
    (hn : 0 < bs.size) : mm.canWrite p bs.size = true := by
  unfold Mem.write at h
  have hne : bs.isEmpty = false := by
    rw [Bool.eq_false_iff]; intro h'; rw [Array.isEmpty_iff_size_eq_zero] at h'; omega
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
  unfold Mem.canWrite
  cases hf : mm.find? p.blk with
  | none => simp [hf] at h
  | some a =>
    simp only [hf] at h ⊢
    simp at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := h
    simp [h1, h2, h3, h4]

theorem setReg_zero {s : LocState} {x : Val} : s.setReg zeroReg x = s := by
  simp [LocState.setReg]

theorem retypeL_mem {mm : Mem} : Val.retypeL .mem (.mem mm) = .mem mm := rfl

/-- `writeParts` without registers changes nothing when no component is the flags and every
memory component is the current memory. -/
theorem writeParts_noop {s : LocState} :
    ∀ (ts : List Ty) (xs : List Val),
      (∀ k (ht : k < ts.length) (hx : k < xs.length),
        ts[k].isFlags = false ∧ (memTy ts[k] = true → xs[k] = s.mem)) →
      s.writeParts ts xs [] = s
  | [], _, _ => by simp [LocState.writeParts]
  | _ :: _, [], _ => by simp [LocState.writeParts]
  | t :: ts, x :: xs, h => by
    have ih := writeParts_noop ts xs (fun k ht hx => h (k + 1) (by simpa using ht) (by simpa using hx))
    obtain ⟨hf, hm⟩ := h 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at hf hm
    cases t with
    | mem =>
      have hx : x = s.mem := hm rfl
      subst hx
      simpa [LocState.writeParts] using ih
    | _ => simp_all [LocState.writeParts]

theorem retypePre_widen : ∀ (ts : List Ty) (xs : List Val), ts.length = xs.length →
    Val.retypePre ts (Val.widenList ts xs) =
      some (List.zipWith (fun t x => (x.widen t).retype t) ts xs)
  | [], [], _ => rfl
  | t :: ts, x :: xs, h => by
    simp only [Val.widenList, Val.retypePre, List.zipWith_cons_cons]
    rw [retypePre_widen ts xs (by simpa using h)]
    rfl

/-- `MakeResult` writes nothing that changes the state (`resultsTy`). -/
theorem write_result_noop {lc : LocCtx} {s : LocState} {mm : Mem} {vid : ID} {args : Array ID}
    {argv : List Val} (hl : lc.ctx.f.lowered = true) (hmm : s.mem = .mem mm)
    (hh : lc.home vid = none ∨ lc.home vid = some (.results #[]))
    (hty : resultsTy lc args (lc.ty vid) = true)
    (hmem : ∀ a ∈ args.toList, memTy (lc.ty a) = true → lc.home a = none)
    (hargv : args.toList.mapM (s.read lc) = .ok argv) :
    s.write lc vid ((Val.tuple argv).retypeL (lc.ty vid)) = s := by
  obtain ⟨hlen, hk⟩ := mapM_res hargv
  cases hT : lc.ty vid with
  | tuple ts =>
    rw [hT] at hty
    simp only [resultsTy, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hty
    obtain ⟨htl, hall⟩ := hty
    have hlen' : ts.length = argv.length := by rw [htl, hlen]; simp
    have hw : (Val.tuple argv).retypeL (.tuple ts) =
        .tuple (List.zipWith (fun t x => (x.widen t).retype t) ts argv) := by
      simp only [Val.retypeL, Val.widen, Val.retype, retypePre_widen ts argv hlen']
    have hreg : ((lc.home vid).map Location.regList).getD [] = [] := by
      rcases hh with h | h <;> simp [h, Location.regList]
    have hw2 : s.write lc vid ((Val.tuple argv).retypeL (.tuple ts)) =
        s.writeParts ts (List.zipWith (fun t x => (x.widen t).retype t) ts argv) [] := by
      rw [hw]
      unfold LocState.write
      rw [hT]
      rcases hh with h | h
      · simp only [h, Val.partsOf]; rfl
      · simp only [h]
        simp [Val.partsOf, Location.regList]
    rw [hw2]
    refine writeParts_noop ts _ (fun k hkt hkx => ?_)
    have hka : k < args.toList.length := by rw [← hlen]; simp at hkx; omega
    have hz := hall (ts[k], args.toList[k]) (List.mem_iff_getElem.2 ⟨k, by simp; omega, by simp⟩)
    simp only [Bool.not_eq_true', Bool.or_eq_true] at hz
    refine ⟨by simpa using hz.1, fun hmt => ?_⟩
    simp only [List.getElem_zipWith]
    have hamt : memTy (lc.ty args.toList[k]) = true := by
      rcases hz.2 with h | h
      · rw [hmt] at h; cases h
      · exact h
    have hrd := hk k hka (by omega)
    rw [read_mem hl (hmem _ (List.getElem_mem hka) hamt) hamt hmm] at hrd
    have hx : argv[k] = .mem mm := (Res.ok.inj hrd).symm
    rw [hx, memTy_eq hmt, hmm]
    rfl
  | _ => rw [hT] at hty; simp [resultsTy] at hty

/-! ## One value: the machine side -/

section Ops

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s : LocState} {b : ID} {i : Nat} {m : MState}

/-- The static facts of an accepted function and its activation. -/
structure Facts (lc : LocCtx) (sym : Nat → BitVec 64) (text : BitVec 64) (az ez : Int)
    (ps : List Prog) (ret : BitVec 64) (E : MatchEnv) : Prop where
  lowered : lc.ctx.f.lowered = true
  /-- A value homed in a register (other than `ZERO`) has a width class. -/
  clsReg : ∀ i r, lc.home i = some (.reg r) → r ≠ zeroReg → (cls (lc.ty i)).isSome = true
  nodup : (ps.map (·.id)).Nodup
  lt : ∀ p ∈ ps, p.id < 2 ^ 32
  ret : ∀ p ∈ ps, (Link.byId sym text az ez ps).addr p.id ≠ some ret
  addr : AddrAgree E.ι

theorem pc_eta (hm : LocMatch E s b i m) {j : Nat} {ps : List Prog}
    (hj : E.pcOf b i = pcAt text ps j) : ({ m with pc := pcAt text ps j } : MState) = m := by
  rw [← hj, ← hm.pc]

/-- A value with no code. -/
theorem op_none {s' : LocState} (hm : LocMatch E s b i m) (hinv : CoreInv E.ι P K s) (hs : s' = s)
    (hpc : E.pcOf b (i + 1) = E.pcOf b i) (hKL : KLe K' K) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι P K' s' ∧ s'.slots = s.slots :=
  ⟨m, .refl, hs ▸ locMatch_pc hm (hpc.trans hm.pc.symm), hs ▸ hinv.mono hKL, hs ▸ rfl⟩

/-- A value whose one Prog writes its register. -/
theorem op_reg (F : Facts lc sym text az ez psA.toList ret E) (hm : LocMatch E s b i m)
    (hinv : CoreInv E.ι P K s) {j j' : Nat} (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') {sh : Shape} (hone : OneAt psA j sh j')
    {r c kd : Nat} {x : Val} {val : BitVec 64} (hd : destOK r = true)
    (hkd : kd < 32) (hrk : objOf? r = some (GoFV.Asm.ARM64.REG_R0 + kd))
    (hx : ValRel E.ι x val) (hfx : Fits c x) (hKL : KLe K' (kSet K r (some c)))
    (hstep : ∀ k (hk : k < psA.toList.length), sh.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m.wX (BitVec.ofNat 5 kd) val with pc := pcAt text psA.toList (k + 1) }) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E (s.setReg r x) b (i + 1) m' ∧ CoreInv E.ι P K' (s.setReg r x) ∧
      (s.setReg r x).slots = s.slots := by
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt (H := H) F.nodup F.lt F.ret rfl hone m
  rw [pc_eta hm hj] at hstar
  obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv hd hkd hrk hx hfx (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  exact ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl (hstep k hk hok)), hlm,
    hinv'.mono hKL, rfl⟩

/-- A value whose one Prog sets the flags. -/
theorem op_flags (F : Facts lc sym text az ez psA.toList ret E) (hm : LocMatch E s b i m)
    (hinv : CoreInv E.ι P K s) {j j' : Nat} (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') {sh : Shape} (hone : OneAt psA j sh j')
    {f : Val} {nz : Flags} (hf : FlagsRel f nz) (hKL : KLe K' K)
    (hstep : ∀ k (hk : k < psA.toList.length), sh.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m with nzcv := nz, pc := pcAt text psA.toList (k + 1) }) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E { s with flags := f } b (i + 1) m' ∧ CoreInv E.ι P K' { s with flags := f } ∧
      ({ s with flags := f } : LocState).slots = s.slots := by
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt (H := H) F.nodup F.lt F.ret rfl hone m
  rw [pc_eta hm hj] at hstar
  have hlm := locMatch_setFlags hm hf (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  exact ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl (hstep k hk hok)), hlm,
    (core_setFlags hinv).mono hKL, rfl⟩

/-- A value whose one Prog stores, outside the addresses `P`. -/
theorem op_mem (F : Facts lc sym text az ez psA.toList ret E) (hm : LocMatch E s b i m)
    (hinv : CoreInv E.ι P K s) (hkeep : Keeps E P s m) {j j' : Nat}
    (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') {sh : Shape} (hone : OneAt psA j sh j')
    {mm' : Mem} {M : Memory} (hM : MemInj E.ι mm' M) (hkn : KeysNodup mm')
    (hsep : SepFrom E.ι P mm') (hP : ∀ y, P y → M y = m.mem y) (hKL : KLe K' K)
    (hstep : ∀ k (hk : k < psA.toList.length), sh.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m with mem := M, pc := pcAt text psA.toList (k + 1) }) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E { s with mem := .mem mm' } b (i + 1) m' ∧
      CoreInv E.ι P K' { s with mem := .mem mm' } ∧
      ({ s with mem := .mem mm' } : LocState).slots = s.slots := by
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt (H := H) F.nodup F.lt F.ret rfl hone m
  rw [pc_eta hm hj] at hstar
  obtain ⟨hsl, hfr⟩ := hkeep M hP
  have hlm := locMatch_setMem hm hsl hfr hM (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  exact ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl (hstep k hk hok)), hlm,
    (⟨hinv.regs, ⟨mm', rfl, hkn, hsep⟩⟩ : CoreInv E.ι P K { s with mem := .mem mm' }).mono hKL, rfl⟩

/-- A register argument `i` of a value that reads it holds its class, by `KRead`. -/
theorem kread_arg {v : Value} (hR : KRead lc v K) (hop : v.op ≠ .Phi) {n a r c : Nat}
    (ha : v.args[n]? = some a) (hh : lc.home a = some (.reg r)) (hc : cls (lc.ty a) = some c) :
    r ≠ zeroReg → K r = some c :=
  fun hr => hR hop a (Array.mem_toList_iff.2 (Array.mem_of_getElem? ha)) r c hh hr hc

/-- One value, from the facts the checker gives about it: from the invariant at the class map
`K`, whose read registers hold their classes (`KRead`), to the invariant at any class map `K'`
that follows `K` across the value (`KNext`). -/
theorem value_core {env : Env} (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι P K s) (hkeep : Keeps E P s m) {v : Value}
    {s' : LocState} {kd : VKind}
    {j j' : Nat} (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') (hvs : VStep psA kd j j')
    (hVK : VK lc v kd) (htemp : (lc.temps[v.id]?).join = none) (hpre : G1Pre lc s v)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι P K' s' ∧ s'.slots = s.slots := by
  have hl := F.lowered
  have hA := F.addr
  have hnone : ∀ {r : Nat}, lc.home v.id = none → r ≠ zeroReg → lc.home v.id ≠ some (.reg r) :=
    fun h _ => by rw [h]; nofun
  cases hVK with
  | phi hop _ =>
    exact op_none hm hinv (stepLoc_phi hop hs) (by rw [hj', hj, show j' = j from hvs])
      (knext_same hK (Or.inl hop))
  | zero hop _ hh hc =>
    obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.1 hc
    obtain ⟨argv, -, rfl⟩ := stepLoc_pure hl htemp (Or.inl hop) hs
    exact op_none hm hinv (by rw [write_reg hh hc', setReg_zero])
      (by rw [hj', hj, show j' = j from hvs])
      (knext_same hK (Or.inr fun r hr => by rw [hh]; simpa using Ne.symm hr))
  | inl hop hh hi =>
    exact op_none hm hinv (stepLoc_inlMark htemp hop hh hi hs)
      (by rw [hj', hj, show j' = j from hvs]) (knext_same hK (Or.inr fun _ => hnone hh))
  | copyMem hop hmt hsz hma hh =>
    obtain ⟨a, ha0, hamt, hah⟩ := memArg_spec hma
    obtain ⟨x, hx, rfl⟩ := stepLoc_copy hl htemp hop (arr1 hsz ha0) hs
    obtain ⟨mm, hmm, -⟩ := hm.mem
    rw [read_mem hl hah hamt hmm] at hx
    cases hx
    refine op_none hm hinv ?_ (by rw [hj', hj, show j' = j from hvs])
      (knext_same hK (Or.inr fun _ => hnone hh))
    rw [write_mem hh hmt, memTy_eq hmt, retypeL_mem, ← hmm]
  | copySame hop hmt hsz hao hro =>
    obtain ⟨a, r1, ha0, hah, hor1, hca⟩ := argObj_spec hao
    obtain ⟨r2, hvh, hd, hor2, hcv⟩ := resObj_spec hro
    obtain rfl := objOf?_inj hor1 hor2
    obtain ⟨k, hk32, ho, hkk⟩ := objOf?_some hor1
    rw [ho] at hor1
    have hnp : v.op ≠ .Phi := by rw [hop]; nofun
    obtain ⟨x, hx, hxv, hxf⟩ := arg_rel hA hl hm hinv hah hca (kread_arg hR hnp ha0 hah hca) hkk
    obtain ⟨x', hx', rfl⟩ := stepLoc_copy hl htemp hop (arr1 hsz ha0) hs
    rw [hx] at hx'
    cases hx'
    rw [write_reg hvh hcv]
    obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv hd hk32 hor1
      (valRel_retypeL hA hcv hxf hxv) (fits_retypeL hcv _) (b' := b) (i' := i + 1)
    rw [wX_rX_self, hj', show j' = j from hvs, ← hj, ← hm.pc] at hlm
    exact ⟨m, .refl, hlm, hinv'.mono (knext_set hK hnp hvh hcv), rfl⟩
  | copyMov hop hmt hsz hao hro hne =>
    obtain ⟨a, r1, ha0, hah, hor1, hca⟩ := argObj_spec hao
    obtain ⟨r2, hvh, hd, hor2, hcv⟩ := resObj_spec hro
    obtain ⟨ka, hka, rfl, hkka⟩ := objOf?_some hor1
    obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor2
    subst hrd
    have hnp : v.op ≠ .Phi := by rw [hop]; nofun
    obtain ⟨x, hx, hxv, hxf⟩ := arg_rel hA hl hm hinv hah hca (kread_arg hR hnp ha0 hah hca) hkka
    obtain ⟨x', hx', rfl⟩ := stepLoc_copy hl htemp hop (arr1 hsz ha0) hs
    rw [hx] at hx'
    cases hx'
    rw [write_reg hvh hcv]
    exact op_reg F hm hinv hj hj' hvs hd hkd hor2 (valRel_retypeL hA hcv hxf hxv)
      (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k hk hok => by
        obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
        rw [progStep_movReg hka hkd (nextAddr_pcAt F.nodup hk) has hf ht, wX_pc] <;> rfl)
  | result hop hh hty hmem _ =>
    obtain ⟨argv, hargv, rfl⟩ := stepLoc_makeResult hl htemp hop hs
    obtain ⟨mm, hmm, -⟩ := hm.mem
    exact op_none hm hinv (write_result_noop hl hmm hh hty hmem hargv)
      (by rw [hj', hj, show j' = j from hvs])
      (knext_same hK (Or.inr fun r _ => by rcases hh with h | h <;> rw [h] <;> nofun))
  | movConst hop hsz hro hb1 =>
    obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
    obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
    subst hrd
    obtain ⟨argv, -, rfl⟩ := stepLoc_pure hl htemp (Or.inr (Or.inl hop)) hs
    rw [write_reg hvh hcv, hop]
    have he : Arm64.evalPure .ARM64MOVDconst (lc.ty v.id) v.auxInt v.aux argv =
        Arm64.res (lc.ty v.id) (BitVec.ofInt 64 v.auxInt.toInt) := rfl
    rw [he]
    refine op_reg F hm hinv hj hj' hvs hd hkd hor
      (valRel_res_const hcv (fun h1 => ?_)) (fits_retypeL hcv _)
      (knext_set hK (by rw [hop]; nofun) hvh hcv) (fun k hk hok => by
        obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
        rw [progStep_movConst hkd (nextAddr_pcAt F.nodup hk) has hf ht, wX_pc] <;> rfl)
    rcases hb1 h1 with h | h <;> rw [h] <;> decide
  | alu hop hsz hao hbo hro h8 hca hcb =>
    obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
    obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
    obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
    obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
    obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
    obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
    subst hrd
    have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
    obtain ⟨x, hx, hxv, hxf⟩ :=
      arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
    obtain ⟨y, hy, hyv, hyf⟩ :=
      arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
    have hKL := knext_set hK hnp hvh hcv
    obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure hl htemp
      (by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]) hs
    rw [arr2 hsz ha0 ha1] at hargv
    obtain rfl := mapM_res_two hargv hx hy
    rw [write_reg hvh hcv]
    have ht := cls_ne_bool hcv h8
    rcases hop with ⟨hop, rfl⟩ | ⟨hop, rfl⟩
    · have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x, y] =
          Arm64.add (lc.ty v.id) [x, y] := by rw [hop]; rfl
      rw [he]
      exact op_reg F hm hinv hj hj' hvs hd hkd hor
        (valRel_retypeL_lo hA hcv ht (lo_add hA hxv hyv hxf hyf h8 hca hcb ht))
        (fits_retypeL hcv _) hKL (fun k hk hok => by
          obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
          rw [progStep_aluReg hkn hkm hkd (nextAddr_pcAt F.nodup hk) (Or.inl has) hf hr ht', wX_pc]
          simp only [has, ↓reduceIte]
          rfl)
    · have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x, y] =
          Arm64.sub (lc.ty v.id) [x, y] := by rw [hop]; rfl
      rw [he]
      exact op_reg F hm hinv hj hj' hvs hd hkd hor
        (valRel_retypeL_lo hA hcv ht
          (lo_sub hA hxv hyv hxf hyf h8 hca hcb ht (hpre.2.2 hop a0 a1 x y ha0 ha1 hx hy)))
        (fits_retypeL hcv _) hKL (fun k hk hok => by
          obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
          rw [progStep_aluReg hkn hkm hkd (nextAddr_pcAt F.nodup hk) (Or.inr has) hf hr ht', wX_pc]
          simp only [has, reduceCtorEq, ↓reduceIte]
          rfl)
  | aluK hop hsz hao hro h8 hca =>
    obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
    obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
    obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
    obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
    subst hrd
    have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
    obtain ⟨x, hx, hxv, hxf⟩ :=
      arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
    have hKL := knext_set hK hnp hvh hcv
    obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure hl htemp
      (by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]) hs
    rw [arr1 hsz ha0] at hargv
    obtain rfl := mapM_res_one hargv hx
    rw [write_reg hvh hcv]
    have ht := cls_ne_bool hcv h8
    rcases hop with ⟨hop, rfl⟩ | ⟨hop, rfl⟩
    · have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x] =
          Arm64.addK (lc.ty v.id) (BitVec.ofInt 64 v.auxInt.toInt) [x] := by rw [hop]; rfl
      rw [he]
      exact op_reg F hm hinv hj hj' hvs hd hkd hor
        (valRel_retypeL_lo hA hcv ht (lo_addK hA hxv hxf h8 hca ht))
        (fits_retypeL hcv _) hKL (fun k hk hok => by
          obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
          rw [progStep_aluConst hkn hkd (nextAddr_pcAt F.nodup hk) (Or.inl has) hf hr ht', wX_pc]
          simp only [has, ↓reduceIte]
          rfl)
    · have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x] =
          Arm64.addK (lc.ty v.id) (-BitVec.ofInt 64 v.auxInt.toInt) [x] := by rw [hop]; rfl
      rw [he]
      have hlo := lo_addK hA hxv hxf h8 hca ht (k := -BitVec.ofInt 64 v.auxInt.toInt) (t := lc.ty v.id)
      rw [← BitVec.sub_eq_add_neg] at hlo
      exact op_reg F hm hinv hj hj' hvs hd hkd hor
        (valRel_retypeL_lo hA hcv ht hlo)
        (fits_retypeL hcv _) hKL (fun k hk hok => by
          obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
          rw [progStep_aluConst hkn hkd (nextAddr_pcAt F.nodup hk) (Or.inr has) hf hr ht', wX_pc]
          simp only [has, reduceCtorEq, ↓reduceIte]
          rfl)
  | cmp hop hsz hfl hhn hao hbo =>
    obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
    obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
    obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
    obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
    have hnp : v.op ≠ .Phi := by rw [hop]; nofun
    obtain ⟨x, hx, hxv, hxf⟩ :=
      arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
    obtain ⟨y, hy, hyv, hyf⟩ :=
      arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
    obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure hl htemp (by simp [hop]) hs
    have hargs := arr2 hsz ha0 ha1
    rw [hargs] at hargv
    obtain rfl := mapM_res_two hargv hx hy
    have hpx := hpre.1 (Or.inl hop) a0 (by simp [hargs]) x hx
    have hpy := hpre.1 (Or.inl hop) a1 (by simp [hargs]) y hy
    have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x, y] = Arm64.cmp x y := by
      rw [hop]; rfl
    rw [write_flags hhn hfl, he, isFlags_eq hfl]
    exact op_flags F hm hinv hj hj' hvs (flagsRel_cmp hA hxv hyv hxf hyf hpx hpy)
      (knext_same hK (Or.inr fun _ => hnone hhn)) (fun k hk hok => by
        obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
        rw [progStep_cmp hkn (nextAddr_pcAt F.nodup hk) has (by rw [hf]; exact ctx_src_reg hkm) hr]
          <;> rfl)
  | cmpK hop hsz hfl hhn hao =>
    obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
    obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
    obtain ⟨x, hx, hxv, hxf⟩ :=
      arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR (by rw [hop]; nofun) ha0 hah0 hca0) hkkn
    obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure hl htemp (by simp [hop]) hs
    have hargs := arr1 hsz ha0
    rw [hargs] at hargv
    obtain rfl := mapM_res_one hargv hx
    have hpx := hpre.1 (Or.inr hop) a0 (by simp [hargs]) x hx
    have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x] =
        Arm64.cmp x (.int .w64 (BitVec.ofInt 64 v.auxInt.toInt)) := by rw [hop]; rfl
    rw [write_flags hhn hfl, he, isFlags_eq hfl]
    exact op_flags F hm hinv hj hj' hvs
      (flagsRel_cmp hA hxv (Or.inl rfl) hxf rfl hpx (fun _ h => by cases h))
      (knext_same hK (Or.inr fun _ => hnone hhn)) (fun k hk hok => by
        obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
        rw [progStep_cmp hkn (nextAddr_pcAt F.nodup hk) has (by rw [hf]; exact ctx_src_const) hr]
          <;> rfl)
  | load hop hsz haux hao hma hro h8 =>
    obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
    obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
    obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
    obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
    obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
    subst hrd
    obtain ⟨mm, hmm, hMI⟩ := hm.mem
    have hnp : v.op ≠ .Phi := by rw [hop]; nofun
    obtain ⟨x, hx, hxv, hxf⟩ :=
      arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
    obtain ⟨x', hx', rfl⟩ := stepLoc_load hl htemp hop (arr2 hsz ha0 ha1) haux
      (read_mem hl hah1 hamt hmm) hs
    rw [hx] at hx'
    cases hx'
    obtain ⟨p, mm2, bs, haddr, hmm2, hrd⟩ := hpre.2.1 hop a0 x ha0 hx
    rw [hmm] at hmm2
    cases hmm2
    obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by decide : 0 < 8)
      (Or.inr (by rw [hrd]; rfl))
    have ht := cls_ne_bool hcv h8
    rw [write_reg hvh hcv, haddr]
    simp only [Option.elim]
    rw [loadN_eq ht]
    exact op_reg F hm hinv hj hj' hvs hd hkd hor
      (valRel_retypeL_lo hA hcv ht ((lo_load hA hMI hpa hrd).mono (cls_le hcv)))
      (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k hk hok => by
        obtain ⟨has, hf, -, ht', hsc⟩ := Shape.ok_eq hok
        have haeq' : ({ m with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kn) +
            BitVec.ofInt 64 v.auxInt.toInt = a + p.off := haeq
        rw [progStep_load hkn hkd (nextAddr_pcAt F.nodup hk) has hf hsc ht'
          (by rw [haeq']; exact hnil), haeq', wX_pc])
  | store hop hsz haux hmt hhn hao hso hma hcs =>
    obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
    obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hso
    obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
    obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
    obtain ⟨ks, hks, rfl, hkks⟩ := objOf?_some hor1
    obtain ⟨mm, hmm, hMI⟩ := hm.mem
    have hnp : v.op ≠ .Phi := by rw [hop]; nofun
    obtain ⟨x, hx, hxv, hxf⟩ :=
      arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
    obtain ⟨y, hy, hyv, hyf⟩ :=
      arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkks
    obtain ⟨x', y', p, mm', hx', hy', haddr, hw, rfl⟩ := stepLoc_store hl htemp hop
      (arr3 hsz ha0 ha1 ha2) haux (read_mem hl hah2 hamt hmm) hs
    rw [hx] at hx'
    cases hx'
    rw [hy] at hy'
    cases hy'
    obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by decide : 0 < 8)
      (Or.inl (by
        have := canWrite_of_write hw (by rw [storeBytes_size8]; decide)
        rwa [storeBytes_size8] at this))
    obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
    rw [hmm] at hmm0
    cases hmm0
    have hyf' : Fits 64 y ∨ Fits 1 y := by rcases hcs with rfl | rfl <;> simp [hyf]
    obtain ⟨hM', hk', hback, al, hal, hoff, hout⟩ := memInj_store hA hMI hk0 hpa hyv hyf' hw
    rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
    have hsep' : SepFrom E.ι P mm' := by
      intro b2 al2 a2 hb hι y hy
      obtain ⟨al1, hb1, hs1⟩ := hback b2 al2 hb
      rw [← hs1]; exact hsep0 b2 al1 a2 hb1 hι y hy
    exact op_mem F hm hinv hkeep hj hj' hvs hM' hk' hsep'
      (fun y hy => hout y fun j hj he => hsep0 _ _ _ hal hpa y hy ⟨by omega, by omega⟩)
      (knext_same hK (Or.inr fun _ => hnone hhn)) (fun k hk hok => by
        obtain ⟨has, hf, -, ht', hsc⟩ := Shape.ok_eq hok
        have haeq' : ({ m with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kn) +
            BitVec.ofInt 64 v.auxInt.toInt = a + p.off := haeq
        rw [progStep_store hkn hks (nextAddr_pcAt F.nodup hk) has hf hsc ht'
          (by rw [haeq']; exact hnil), haeq']
        rfl)

end Ops

/-! ## Terminators -/

private def stageBody (lc : LocCtx) (s : LocState) (c : ID) (regs : Array (Option Val)) :
    Res (ForInStep (Array (Option Val))) := do
  let x ← s.control lc c
  pure (ForInStep.yield (if c < regs.size then regs.set! c (some x) else regs))

private theorem stepTermLoc_eq' (lc : LocCtx) (s : LocState) (b : Block) :
    stepTermLoc lc s b =
      (forIn b.controls.toList s.fr.regs (stageBody lc s)) >>= fun regs =>
        (stepTermL ({ s with fr := { s.fr with regs } } : LocState).fr b) >>= fun n =>
          pure (n, ({ s with fr := { s.fr with regs } } : LocState)) := by
  unfold stepTermLoc
  rw [Array.forIn_toList]
  rfl

/-- `stepTermLoc` only stages the controls. -/
theorem stepTermLoc_gen {lc : LocCtx} {s : LocState} {blk : Block} {n : Next} {s' : LocState}
    (h : stepTermLoc lc s blk = .ok (n, s')) :
    ∃ R, s' = { s with fr := { s.fr with regs := R } } ∧ stepTermL s'.fr blk = .ok n := by
  rw [stepTermLoc_eq'] at h
  generalize forIn blk.controls.toList s.fr.regs (stageBody lc s) = r at h
  cases r with
  | ok R =>
    simp only [bind, Res.bind] at h
    generalize hn : stepTermL _ blk = r at h
    cases r with
    | ok n' => cases h; exact ⟨R, rfl, hn⟩
    | panic e m => cases h
    | stuck msg => cases h
  | panic e m => cases h
  | stuck msg => cases h

/-- `stepTermLoc` of a block with one control: the control read and staged. -/
theorem stepTermLoc_one {lc : LocCtx} {s : LocState} {blk : Block} {n : Next} {s' : LocState}
    {c : ID} (hc : blk.controls = #[c]) (h : stepTermLoc lc s blk = .ok (n, s')) :
    ∃ x R, s.control lc c = .ok x ∧ s' = { s with fr := { s.fr with regs := R } } ∧
      (∀ y, Sem.control s'.fr blk 0 = .ok y → y = x) ∧ stepTermL s'.fr blk = .ok n := by
  rw [stepTermLoc_eq', hc] at h
  cases hx : s.control lc c with
  | ok x =>
    simp only [List.forIn_cons, List.forIn_nil, stageBody, hx, bind, Res.bind, pure] at h
    generalize hn : stepTermL _ blk = r at h
    cases r with
    | ok n' =>
      cases h
      refine ⟨x, _, rfl, rfl, fun y hy => ?_, hn⟩
      simp only [Sem.control, hc] at hy
      by_cases hlt : c < s.fr.regs.size
      · simp [hlt, Array.set!_eq_setIfInBounds, Res.ofOption] at hy
        exact hy.symm
      · simp [hlt, Res.ofOption] at hy
    | panic e m => cases h
    | stuck msg => cases h
  | panic e m => simp [List.forIn_cons, stageBody, hx, bind, Res.bind] at h
  | stuck msg => simp [List.forIn_cons, stageBody, hx, bind, Res.bind] at h

/-- A control is read from its home, or is a `MakeResult`'s tuple at the control's shape. -/
theorem control_cases {lc : LocCtx} {s : LocState} {c : ID} {x : Val}
    (h : s.control lc c = .ok x) :
    s.read lc c = .ok x ∨ ∃ xs, x = (LMode.loc lc.ctx.f).retype (lc.ty c) (Val.tuple xs) := by
  unfold LocState.control at h
  split at h
  · split at h
    · right
      simp only [bind, Res.bind] at h
      split at h
      · cases h; exact ⟨_, rfl⟩
      · cases h
      · cases h
    · exact Or.inl h
  · cases h

theorem retypeL_tuple_reg {t : Ty} {c : Nat} (hc : cls t = some c) (xs : List Val) :
    (Val.tuple xs).retypeL t = .poison := by
  cases t <;> simp_all [Gen.Check.cls] <;> rfl

theorem retypeL_tuple_flags (xs : List Val) : (Val.tuple xs).retypeL Ty.flags = .poison := rfl

theorem condBr_arm {k : BlockKind} {p : As × As} (h : condBr k = some p) :
    k.isArm64 = true ∧ k ≠ .ARM64JUMPTABLE := by
  unfold condBr at h
  split at h <;> first | (cases h; exact ⟨rfl, by decide⟩) | cases h

theorem zeroBr_arm {k : BlockKind} {p : As × As} (h : zeroBr k = some p) :
    k.isArm64 = true ∧ k ≠ .ARM64JUMPTABLE := by
  unfold zeroBr at h
  split at h <;> first | (cases h; exact ⟨rfl, by decide⟩) | cases h

/-- An arm64 conditional block other than a jump table branches on `Arm64.taken`. -/
theorem stepTermL_arm {fr : GoFV.SSA.Sem.Frame} {b : Block} {n : Next} (ha : b.kind.isArm64 = true)
    (hj : b.kind ≠ .ARM64JUMPTABLE) (h : stepTermL fr b = .ok n) :
    ∃ y t, Sem.control fr b 0 = .ok y ∧ Arm64.taken b.kind b.auxInt y = some t ∧
      succ b (if t then 0 else 1) = .ok n := by
  unfold stepTermL at h
  simp only [ha, ↓reduceIte, bind, Res.bind] at h
  split at h
  · rename_i y hy
    dsimp only at h
    split at h
    · exact ⟨y, true, hy, by assumption, h⟩
    · exact ⟨y, false, hy, by assumption, h⟩
    · cases h
  · cases h
  · cases h

theorem stepTermL_plain {fr : GoFV.SSA.Sem.Frame} {b : Block} {n : Next} (hk : b.kind = .Plain)
    (h : stepTermL fr b = .ok n) : succ b 0 = .ok n := by
  unfold stepTermL stepTerm at h
  simpa [BlockKind.isArm64, hk] using h

theorem stepTermL_ret {fr : GoFV.SSA.Sem.Frame} {b : Block} {e : Edge} (hk : b.kind = .Ret)
    (h : stepTermL fr b = .ok (.goto e)) : False := by
  unfold stepTermL stepTerm at h
  simp only [hk, BlockKind.isArm64, Bool.false_eq_true, ↓reduceIte, bind, Res.bind] at h
  generalize Sem.control fr b 0 = r at h
  cases r with
  | ok x =>
    dsimp only at h
    split at h
    · split at h
      · split at h <;> cases h
      · cases h
    · cases h
  | panic => cases h
  | stuck => cases h

theorem succ_two {b : Block} {e0 e1 : Edge} (hs : b.succs = #[e0, e1]) {t : Bool} {n : Next}
    (h : succ b (if t then 0 else 1) = .ok n) : n = .goto (if t then e0 else e1) := by
  cases t <;> simp [succ, hs, Res.ofOption] at h <;> exact h.symm

section Term

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {ret : BitVec 64}
  {E : MatchEnv} {cx : Cx} {tab : PcTab}

/-- Every block starts at the index its `startIdx` gives, where `pcOf` points. -/
def Starts (cx : Cx) (text : BitVec 64) (E : MatchEnv) : Prop :=
  ∀ n ∈ cx.lc.ctx.f.blocks.toList,
    ∃ j0, cx.startIdx n = .ok j0 ∧ E.pcOf n 0 = pcAt text cx.ps.toList j0

theorem start_of_mem (hblocks : cx.blocks cx.lc.ctx.f.blocks.toList = .ok tab)
    (hpcOf : E.pcOf = pcOfTab text cx.ps.toList tab) : Starts cx text E := by
  intro n hn
  obtain ⟨b, j, js, e, next, -, hj, hvals, -, -, hrow⟩ := Cx.blocks_spec hblocks n hn
  obtain ⟨-, h0, -⟩ := Cx.values_spec hvals
  exact ⟨j, hj, by rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some, h0]⟩

theorem target_pc {n : ID} {j0 id : Nat} (hj : cx.startIdx n = .ok j0) (hb : cx.bstart n = some id) :
    (Link.byId sym text az ez cx.ps.toList).addr id = some (pcAt text cx.ps.toList j0) := by
  obtain ⟨id', hb', hj', hid⟩ := Cx.startIdx_spec hj
  rw [hb] at hb'
  cases hb'
  have hj'' : j0 < cx.ps.toList.length := by simpa using hj'
  have : cx.ps.toList[j0] = cx.ps[j0] := by simp
  rw [← hid, ← this]
  exact addr_pcAt hj''

/-- From index `k`: the fall-through to `fb` laid out next, or a `JMP` to it. -/
theorem fall_path (F : Facts cx.lc sym text az ez cx.ps.toList ret E) (hst : Starts cx text E)
    {next : Option (ID × Nat)}
    (hnext : ∀ n k, next = some (n, k) → cx.startIdx n = .ok k) {fb : ID}
    (hfb : fb ∈ cx.lc.ctx.f.blocks.toList) {k : Nat}
    (h : next = some (fb, k) ∨ ∃ fid k', cx.bstart fb = some fid ∧
      OneAt cx.ps k { as := .JMP, to := brA fid } k') (m : MState) :
    PStar H (Link.byId sym text az ez cx.ps.toList) cx.ps.toList ret
      { m with pc := pcAt text cx.ps.toList k } { m with pc := E.pcOf fb 0 } := by
  obtain ⟨j0, hj0, hpc0⟩ := hst fb hfb
  rw [hpc0]
  rcases h with h | ⟨fid, k', hfid, hone⟩
  · rw [hnext _ _ h] at hj0
    cases hj0
    exact .refl
  · obtain ⟨k0, rfl, hk0, hok, hstar⟩ := pstar_oneAt (H := H) F.nodup F.lt F.ret rfl hone m
    obtain ⟨has, -, -, ht, -⟩ := Shape.ok_eq hok
    exact hstar.tail (pstep_at F.nodup F.lt F.ret hk0 rfl
      (progStep_jmp (nextAddr_pcAt F.nodup hk0) has ht (target_pc (text := text) hj0 hfid)))

/-- A two-way branch: the branch Prog goes to `tb` when `d`, else on to `fb`. -/
theorem two_path (F : Facts cx.lc sym text az ez cx.ps.toList ret E) (hst : Starts cx text E)
    {next : Option (ID × Nat)}
    (hnext : ∀ n k, next = some (n, k) → cx.startIdx n = .ok k) {tb fb : ID}
    (htb : tb ∈ cx.lc.ctx.f.blocks.toList) (hfb : fb ∈ cx.lc.ctx.f.blocks.toList) {j : Nat}
    {br : Shape} (h2 : TwoAt cx next j br tb fb) {d : Bool} (m : MState)
    (hstep : ∀ tid T k (hk : k < cx.ps.toList.length), cx.bstart tb = some tid →
      (Link.byId sym text az ez cx.ps.toList).addr tid = some T →
      { br with to := brA tid }.ok cx.ps.toList[k] = true →
      progStep (Link.byId sym text az ez cx.ps.toList) cx.ps.toList[k]
          { m with pc := pcAt text cx.ps.toList k } =
        .ok { m with pc := if d then T else pcAt text cx.ps.toList (k + 1) }) :
    PStar H (Link.byId sym text az ez cx.ps.toList) cx.ps.toList ret
      { m with pc := pcAt text cx.ps.toList j } { m with pc := E.pcOf (if d then tb else fb) 0 } := by
  obtain ⟨tid, k, htid, hone, hrest⟩ := h2
  obtain ⟨k0, rfl, hk0, hok, hstar⟩ := pstar_oneAt (H := H) F.nodup F.lt F.ret rfl hone m
  obtain ⟨jt, hjt, hpct⟩ := hst tb htb
  have hT := target_pc (sym := sym) (text := text) (az := az) (ez := ez) hjt htid
  have hs1 := pstep_at (H := H) F.nodup F.lt F.ret hk0 rfl (hstep tid _ k0 hk0 htid hT hok)
  cases d with
  | true =>
    have := hstar.tail hs1
    simp only [↓reduceIte] at this ⊢
    rw [hpct]
    exact this
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hs1 ⊢
    exact (hstar.tail hs1).trans (fall_path F hst hnext hfb hrest m)

theorem locMatch_jump {s : LocState} {b : ID} {i : Nat} {m : MState} (hm : LocMatch E s b i m)
    {fr : GoFV.SSA.Sem.Frame} {b' : ID} {i' : Nat} :
    LocMatch E { s with fr } b' i' { m with pc := E.pcOf b' i' } :=
  { hm with pc := rfl }

end Term

/-! ## The terminators of a checked block -/

/-- A terminator that goes to a successor, from the facts the checker gives about its block. -/
theorem term_core {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int}
    {ret : BitVec 64} {E : MatchEnv} {cx : Cx} {P : BitVec 64 → Prop} {bid : ID} {blk : Block}
    {e : Edge} {s s' : LocState} {m : MState} {e' : Nat} {next : Option (ID × Nat)}
    (F : Facts cx.lc sym text az ez cx.ps.toList ret E) (hst : Starts cx text E)
    (hterm : TermOK cx blk e' next) (hnext : ∀ n k, next = some (n, k) → cx.startIdx n = .ok k)
    (hpcT : E.pcOf bid blk.values.size = pcAt text cx.ps.toList e')
    (hm : LocMatch E s bid blk.values.size m) {K : Nat → Option Nat} (hinv : CoreInv E.ι P K s)
    (hK : ∀ c r cc, blk.controls[0]? = some c → cx.lc.home c = some (.reg r) → r ≠ zeroReg →
      cls (cx.lc.ty c) = some cc → K r = some cc)
    (hpre : G1TermPre cx.lc s blk) (ht : stepTermLoc cx.lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H (Link.byId sym text az ez cx.ps.toList) cx.ps.toList ret m m' ∧
      LocMatch E s' e.b 0 m' ∧ (∃ R, s' = { s with fr := { s.fr with regs := R } }) ∧
      e ∈ blk.succs.toList ∧ e.b ∈ cx.lc.ctx.f.blocks.toList := by
  have hl := F.lowered
  have hA := F.addr
  have hm0 : ({ m with pc := pcAt text cx.ps.toList e' } : MState) = m := by
    rw [← hpcT, ← hm.pc]
  have hsucc : ∀ x ∈ blk.succs.toList, x.b ∈ cx.lc.ctx.f.blocks.toList := hterm.succs
  have hfin : ∀ (e0 : Edge), e0 ∈ blk.succs.toList → e = e0 →
      (∃ R, s' = { s with fr := { s.fr with regs := R } }) →
      PStar H (Link.byId sym text az ez cx.ps.toList) cx.ps.toList ret m
        { m with pc := E.pcOf e0.b 0 } →
      ∃ m', PStar H (Link.byId sym text az ez cx.ps.toList) cx.ps.toList ret m m' ∧
        LocMatch E s' e.b 0 m' ∧ (∃ R, s' = { s with fr := { s.fr with regs := R } }) ∧
        e ∈ blk.succs.toList ∧ e.b ∈ cx.lc.ctx.f.blocks.toList := by
    rintro e0 he0 rfl ⟨R, rfl⟩ hstar
    exact ⟨_, hstar, locMatch_jump hm, ⟨R, rfl⟩, he0, hsucc _ he0⟩
  by_cases hk : blk.kind = .Plain
  · obtain ⟨e0, hs0, hfall⟩ := hterm.plain hk
    obtain ⟨R, hR, hn⟩ := stepTermLoc_gen ht
    have hsn := stepTermL_plain hk hn
    simp [succ, hs0, Res.ofOption] at hsn
    refine hfin e0 (by simp [hs0]) hsn.symm ⟨R, hR⟩ ?_
    rw [← hm0]
    exact fall_path F hst hnext (hsucc e0 (by simp [hs0])) hfall m
  by_cases hr : blk.kind = .Ret
  · obtain ⟨R, -, hn⟩ := stepTermLoc_gen ht
    exact (stepTermL_ret hr hn).elim
  obtain ⟨e0, e1, c, hs01, hcs, hcase⟩ := hterm.branch hk hr
  have he0 : e0 ∈ blk.succs.toList := by simp [hs01]
  have he1 : e1 ∈ blk.succs.toList := by simp [hs01]
  obtain ⟨x, R, hx, hR, hctl, hn⟩ := stepTermLoc_one hcs ht
  rcases hcase with ⟨asm, inv, hbr, hfl, hhn, htwo⟩ | ⟨asm, inv, r, o, -, hzb, hh, ho, hcl, htwo⟩
  · -- a flags branch
    obtain ⟨harm, hnj⟩ := condBr_arm hbr
    obtain ⟨y, t, hy, htk, hsn⟩ := stepTermL_arm harm hnj hn
    obtain rfl := (hctl y hy).symm
    have hge := succ_two hs01 hsn
    cases hge
    obtain ⟨cc, cc', hca, hci, htaken, hneg⟩ := condBr_spec hbr
    rw [htaken] at htk
    have hxs : x = s.flags.retypeL Ty.flags := by
      rcases control_cases hx with h | ⟨xs, rfl⟩
      · rw [read_flags hl hhn hfl, isFlags_eq hfl] at h
        exact (Res.ok.inj h).symm
      · rw [lmode_retype hl, isFlags_eq hfl, retypeL_tuple_flags] at htk
        cases htk
    subst hxs
    obtain ⟨-, hon⟩ := flags_retypeL hm.flags
    rw [hon] at htk
    have hholds := onVal_holds hm.flags htk
    refine hfin _ (by cases t <;> simp [he0, he1]) rfl ⟨R, hR⟩ ?_
    rw [← hm0]
    rcases htwo with h2 | h2
    · have := two_path (H := H) (d := t) F hst hnext (hsucc e0 he0) (hsucc e1 he1) h2 m
        (fun tid T k hk _ hT hok => by
          obtain ⟨has, -, -, hto, -⟩ := Shape.ok_eq hok
          rw [progStep_bcond (nextAddr_pcAt F.nodup hk) (by rw [has]; exact hca) hto hT]
          simp only [hholds])
      cases t <;> simpa using this
    · have := two_path (H := H) (d := !t) F hst hnext (hsucc e1 he1) (hsucc e0 he0) h2 m
        (fun tid T k hk _ hT hok => by
          obtain ⟨has, -, -, hto, -⟩ := Shape.ok_eq hok
          rw [progStep_bcond (nextAddr_pcAt F.nodup hk) (by rw [has]; exact hci) hto hT]
          simp only [hneg, hholds])
      cases t <;> simpa using this
  · -- a register test
    obtain ⟨harm, hnj⟩ := zeroBr_arm hzb
    obtain ⟨y, t, hy, htk, hsn⟩ := stepTermL_arm harm hnj hn
    obtain rfl := (hctl y hy).symm
    have hge := succ_two hs01 hsn
    cases hge
    have hcls : ∃ cc, Gen.Check.cls (cx.lc.ty c) = some cc ∧ (cc = 64 ∨ cc = 1) := by
      rcases hcl with h | h <;> exact ⟨_, h, by simp⟩
    obtain ⟨cc, hcc, hcc'⟩ := hcls
    obtain ⟨k, hk32, rfl, hkk⟩ := objOf?_some ho
    obtain ⟨x', hx', hxv, hxf⟩ :=
      arg_rel hA hl hm hinv hh hcc (fun hr => hK c r cc (by simp [hcs]) hh hr hcc) hkk
    have hxx : x = x' := by
      rcases control_cases hx with h | ⟨xs, rfl⟩
      · rw [hx'] at h; exact (Res.ok.inj h).symm
      · rw [lmode_retype hl, retypeL_tuple_reg hcc] at htk
        rcases zeroBr_spec hzb with ⟨hz, -, -⟩ | ⟨hz, -, -⟩ <;>
          simp [hz, Arm64.taken, Arm64.isZero, Arm64.reg] at htk
    subst hxx
    have hnb := hpre (by rcases zeroBr_spec hzb with ⟨hz, -⟩ | ⟨hz, -⟩ <;> simp [hz]) c x
      (by simp [hcs]) hx'
    have hfz : Fits 64 x ∨ Fits 1 x := by rcases hcc' with rfl | rfl <;> simp [hxf]
    refine hfin _ (by cases t <;> simp [he0, he1]) rfl ⟨R, hR⟩ ?_
    rw [← hm0]
    rcases zeroBr_spec hzb with ⟨hz, rfl, rfl⟩ | ⟨hz, rfl, rfl⟩
    · -- `Z`: taken when zero
      rw [hz] at htk
      obtain ⟨z, hzx, rfl⟩ : ∃ z, Arm64.isZero x = some z ∧ z = t := ⟨t, htk, rfl⟩
      have hzv := isZero_eq hA hxv hfz hnb hzx
      rcases htwo with h2 | h2
      · have := two_path (H := H) (d := z) F hst hnext (hsucc e0 he0) (hsucc e1 he1) h2 m
          (fun tid T k' hk _ hT hok => by
            obtain ⟨has, hf, -, hto, -⟩ := Shape.ok_eq hok
            have hrx : ({ m with pc := pcAt text cx.ps.toList k' } : MState).rX (BitVec.ofNat 5 k) =
                m.rX (BitVec.ofNat 5 k) := rfl
            rw [progStep_cbz hk32 (nextAddr_pcAt F.nodup hk) (Or.inl has) hf hto hT, hrx, ← hzv,
              show cx.ps.toList[k'].as = As.CBZ from has]
            cases z <;> simp)
        cases z <;> simpa using this
      · have := two_path (H := H) (d := !z) F hst hnext (hsucc e1 he1) (hsucc e0 he0) h2 m
          (fun tid T k' hk _ hT hok => by
            obtain ⟨has, hf, -, hto, -⟩ := Shape.ok_eq hok
            have hrx : ({ m with pc := pcAt text cx.ps.toList k' } : MState).rX (BitVec.ofNat 5 k) =
                m.rX (BitVec.ofNat 5 k) := rfl
            rw [progStep_cbz hk32 (nextAddr_pcAt F.nodup hk) (Or.inr has) hf hto hT, hrx, ← hzv,
              show cx.ps.toList[k'].as = As.CBNZ from has]
            cases z <;> simp)
        cases z <;> simpa using this
    · -- `NZ`: taken when not zero
      rw [hz] at htk
      simp only [Arm64.taken, Option.map_eq_some_iff] at htk
      obtain ⟨z, hzx, rfl⟩ := htk
      have hzv := isZero_eq hA hxv hfz hnb hzx
      rcases htwo with h2 | h2
      · have := two_path (H := H) (d := !z) F hst hnext (hsucc e0 he0) (hsucc e1 he1) h2 m
          (fun tid T k' hk _ hT hok => by
            obtain ⟨has, hf, -, hto, -⟩ := Shape.ok_eq hok
            have hrx : ({ m with pc := pcAt text cx.ps.toList k' } : MState).rX (BitVec.ofNat 5 k) =
                m.rX (BitVec.ofNat 5 k) := rfl
            rw [progStep_cbz hk32 (nextAddr_pcAt F.nodup hk) (Or.inr has) hf hto hT, hrx, ← hzv,
              show cx.ps.toList[k'].as = As.CBNZ from has]
            cases z <;> simp)
        cases z <;> simpa using this
      · have := two_path (H := H) (d := z) F hst hnext (hsucc e1 he1) (hsucc e0 he0) h2 m
          (fun tid T k' hk _ hT hok => by
            obtain ⟨has, hf, -, hto, -⟩ := Shape.ok_eq hok
            have hrx : ({ m with pc := pcAt text cx.ps.toList k' } : MState).rX (BitVec.ofNat 5 k) =
                m.rX (BitVec.ofNat 5 k) := rfl
            rw [progStep_cbz hk32 (nextAddr_pcAt F.nodup hk) (Or.inl has) hf hto hT, hrx, ← hzv,
              show cx.ps.toList[k'].as = As.CBZ from has]
            cases z <;> simp)
        cases z <;> simpa using this

/-! ## The theorems -/

/-- G1's frameless activation without slots keeps any memory change. -/
theorem g1_keeps {E : MatchEnv} {s : LocState} {b : ID} {i : Nat} {m : MState}
    (hm : LocMatch E s b i m) (hleaf : E.framed = false) (hsl : s.slots = []) :
    Keeps E (fun _ => False) s m := by
  intro M _
  refine ⟨fun k v hk => by simp [hsl] at hk, ?_⟩
  obtain ⟨h1, h2, _, h4⟩ := hm.frame
  exact ⟨h1, h2, (fun hf => by rw [hleaf] at hf; cases hf), h4⟩

theorem g1_value {env : Env} {H : Hooks} {lc : LocCtx} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {E : MatchEnv} {bid : ID}
    {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG1 lc ps bstart = .ok tab) (hE : G1Env lc L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp v.op = false) (hm : LocMatch E s bid i m) (hinv : G1Inv lc s)
    (hpre : G1Pre lc s v) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' bid (i + 1) m' ∧ G1Inv lc s' := by
  obtain ⟨-, hlink, hpcOf, hret, hA, hleaf⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨cx, rfl, rfl, -, hl, hhome, hlt, hnd, hblocks⟩ := checkG1_spec hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  obtain ⟨htemp, hVK⟩ := vkind_spec hkd hen
  have hhome' : ∀ i r, cx.lc.home i = some (.reg r) → homeOK cx.lc i = true := fun i _ _ => hhome i
  have F : Facts cx.lc sym text az ez cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home hhome', hnd, hlt, hret, hA⟩
  obtain ⟨m', hstar, hlm, hinv', hsl⟩ := value_core F hm hinv.core
    (g1_keeps hm hleaf hinv.slots)
    (by rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some])
    (by rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]) hvs hVK htemp hpre
    (kread_regCls hhome') (knext_regCls hhome') hs
  exact ⟨m', hstar, hlm, G1Inv.of_core hinv' (hsl.trans hinv.slots)⟩

theorem g1_term {H : Hooks} {lc : LocCtx} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {E : MatchEnv} {bid : ID}
    {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG1 lc ps bstart = .ok tab) (hE : G1Env lc L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m) (hinv : G1Inv lc s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G1Inv lc s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨-, hlink, hpcOf, hret, hA, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨cx, rfl, rfl, -, hl, hhome, hlt, hnd, hblocks⟩ := checkG1_spec hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, hterm, hnext, hrow⟩ :=
    Cx.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨hlen, -, -⟩ := Cx.values_spec hvals
  have F : Facts cx.lc sym text az ez cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home (fun i _ _ => hhome i), hnd, hlt, hret, hA⟩
  have hpcT : E.pcOf bid blk.values.size = pcAt text cx.ps.toList e' := by
    rw [hpcOf]
    simp only [pcOfTab, hrow, Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hlen])]
    simp [hlen]
  obtain ⟨m', hstar, hlm, ⟨R, rfl⟩, -, hmem⟩ := term_core (H := H) F (start_of_mem hblocks hpcOf)
    hterm hnext hpcT hm (hinv.core (ι := E.ι))
    (fun c r cc _ hh hr hcc => regCls_of_home (hhome c) hh hr hcc) hpre ht
  exact ⟨m', hstar, hlm, ⟨hinv.slots, hinv.regs, hinv.mem⟩, hmem⟩

end GoFV.Proof.Gen
