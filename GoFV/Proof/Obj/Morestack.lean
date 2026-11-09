import GoFV.Proof.Obj.Words
import GoFV.Proof.Obj.Spec
import GoFV.Proof.Gen.Mem

variable [GoFV.SSA.Sem.Addrs]

/-!
# The stack check and the morestack path of the prologue (`docs/plans/proofs3.md` §2, row C6/D3)

`stackCheck_run`: from the function's entry the stack check's words reach the end of the check
when it passes (`CheckPasses`) and the morestack tail when it fails.

`symUntil_sound`: the words `symUntil` (`GoFV/Asm/CheckObj.lean`) accepts run as it says, chunk
by chunk (`symWords_sound`).

The morestack tail (`checkTail`, `checkTail_spec`) stores the argument registers in their slots
(`tailPlan`: `off(SP)` of the entry's `SP`), copies `R30` to `R3`, calls `runtime.morestack`,
reloads the registers and branches back to the stack check. `runtime.morestack` is trusted
(`MorestackOK`, the contract of `morestackHook`): it returns to `X30` with `X30` set to `R3`,
`SP`, `R26`, `R28`, `R29` kept, the memory kept but the guard word, and the guard lowered.
`more_loop`: from the entry, round trips through the tail end at the entry in a state whose
stack check passes (induction on the guard); the state is the entry's but for the reloaded
registers (`reloadVal`: the slot's low bytes, extended), the other registers but `R26`, `R28`,
`R29`, `R30`, the slots and the guard word (`MoreStep`).
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.SSA.Sem (MStar MStep)

/-! ## Definitions -/

/-- The stack check with frame size `az` reading `gOff(g)` passes from `s`: the limit (`SP`,
or `SP − (az − StackSmall)` above `StackSmall`) is above the guard, unsigned. -/
def CheckPasses (az : Int) (gOff : Nat) (s : MState) : Prop :=
  (readMem s.mem (s.x 28 + BitVec.ofNat 64 gOff) 8).toNat <
    (if az ≤ 128 then s.sp else s.sp + BitVec.ofInt 64 (-(az - 128))).toNat

instance (az : Int) (gOff : Nat) (s : MState) : Decidable (CheckPasses az gOff s) :=
  Nat.decLt _ _

/-- The guard the stack check reads, `gOff(g)`. -/
def guardOf (gOff : Nat) (s : MState) : Nat :=
  (readMem s.mem (s.x 28 + BitVec.ofNat 64 gOff) 8).toNat

/-- `a` is one of the 8 bytes of the word at `A` (as numbers). -/
def InWord (A a : BitVec 64) : Prop := A.toNat ≤ a.toNat ∧ a.toNat < A.toNat + 8

instance (A a : BitVec 64) : Decidable (InWord A a) := instDecidableAnd

/-- `a` is a byte of a slot of `sl` (`off(sp)`, as numbers). -/
def InSlots (sl : List TailSlot) (sp a : BitVec 64) : Prop :=
  ∃ s ∈ sl, sp.toNat + s.off ≤ a.toNat ∧ a.toNat < sp.toNat + s.off + s.n

/-- The value a register spilled with value `v` in `n` bytes is reloaded with (zero-extended, or
sign-extended if `sg`). -/
def reloadVal (n : Nat) (sg : Bool) (v : BitVec 64) : BitVec 64 :=
  if sg then GoFV.SSA.Sem.Arm64.sext (8 * n) ((v.setWidth (8 * n)).setWidth 64)
  else (v.setWidth (8 * n)).setWidth 64

/-- **The contract of `runtime.morestack`** (trusted; `morestackHook`) at `tgt`, for the stack
check of a frame of `az` bytes reading `gOff(g)` of a function entered in `s0`: `tgt` has no
code and is not the return address; from a state at `tgt` with the entry's `SP`, `g` and stack
bound `0(g)` whose stack check fails, the hook returns to `X30` with `X30` set to `R3`, `SP`,
`R26`, `R28`, `R29` kept, the memory kept but the guard word, and the guard lower. -/
def MorestackOK (H : Hooks) (code : Code) (retM tgt : BitVec 64) (az : Int) (gOff : Nat)
    (s0 : MState) : Prop :=
  code tgt = none ∧ tgt ≠ retM ∧
  ∀ s : MState, s.pc = tgt → s.sp = s0.sp → s.x 28 = s0.x 28 →
    s.word (s.x 28) = s0.word (s0.x 28) → ¬ CheckPasses az gOff s →
    ∃ s', H.call s = some (.ret s') ∧ s'.pc = s.x 30 ∧ s'.sp = s.sp ∧ s'.x 26 = s.x 26 ∧
      s'.x 28 = s.x 28 ∧ s'.x 29 = s.x 29 ∧ s'.x 30 = s.x 3 ∧
      (∀ a, ¬ InWord (s.x 28 + BitVec.ofNat 64 gOff) a → s'.mem a = s.mem a) ∧
      guardOf gOff s' < guardOf gOff s

/-- The caller's side of the morestack path from the entry `s0`: the spill slots (`tailPlan`,
`off(SP)`) lie below `2^64` and apart from `g`'s first 32 bytes (the stack bounds and guards). -/
def TailSep (spills : List Spill) (s0 : MState) : Prop :=
  ∀ sl, tailPlan spills = .ok sl → ∀ s ∈ sl, s0.sp.toNat + s.off + s.n ≤ 2 ^ 64 ∧
    (s0.sp.toNat + s.off + s.n ≤ (s0.x 28).toNat ∨ (s0.x 28).toNat + 32 ≤ s0.sp.toNat + s.off)

/-- `s` is the entry state `s0` after round trips through the morestack tail with slots `sl` and
the guard at `gOff(g)`: at the entry with `SP`, `R26`, `R28`, `R29`, `R30` kept, each reloaded
register its own value or its reload, the memory kept but the slots and the guard word. -/
structure MoreStep (sl : List TailSlot) (gOff : Nat) (s0 s : MState) : Prop where
  pc : s.pc = s0.pc
  sp : s.sp = s0.sp
  x26 : s.x 26 = s0.x 26
  x28 : s.x 28 = s0.x 28
  x29 : s.x 29 = s0.x 29
  x30 : s.x 30 = s0.x 30
  regs : ∀ (k : Reg) (q : TailSlot), reloadOf sl k.toNat = some q →
    s.x k = s0.x k ∨ s.x k = reloadVal q.n q.sg (s0.x k)
  mem : ∀ a, ¬ InSlots sl s0.sp a → ¬ InWord (s0.x 28 + BitVec.ofNat 64 gOff) a →
    s.mem a = s0.mem a

/-- The state `s` where the stack check of the function entered in `s0` passes: `s0` itself, or
(when the function has a stack check) `s0` after round trips through the morestack tail. -/
def MoreRel (check : Option (Nat × Nat × Nat)) (spills : List Spill) (s0 s : MState) : Prop :=
  s = s0 ∨ ∃ ce tail gOff sl, check = some (ce, tail, gOff) ∧ tailPlan spills = .ok sl ∧
    MoreStep sl gOff s0 s

/-- What the morestack path keeps: the PC, `SP`, `R26`, `R28`, `R29`, `R30`. -/
theorem MoreRel.keep {check : Option (Nat × Nat × Nat)} {spills : List Spill} {s0 s : MState}
    (h : MoreRel check spills s0 s) : s.pc = s0.pc ∧ s.sp = s0.sp ∧ s.x 26 = s0.x 26 ∧
      s.x 28 = s0.x 28 ∧ s.x 29 = s0.x 29 ∧ s.x 30 = s0.x 30 := by
  rcases h with rfl | ⟨ce, tail, gOff, sl, -, -, hm⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨hm.pc, hm.sp, hm.x26, hm.x28, hm.x29, hm.x30⟩

/-! ## `symUntil` -/

section Words

variable {base : BitVec 64} {sym : Nat → BitVec 64} {t : ByteArray} {rs : List Reloc}
  {code : Code} {H : Hooks} {retM : BitVec 64}

private theorem ms_unitLen (rs : List Reloc) (o : Nat) : ∃ n, unitLen rs o = n + 1 ∧ n ≤ 1 := by
  unfold unitLen
  split
  · split
    · exact ⟨0, rfl, by omega⟩
    · exact ⟨1, rfl, by omega⟩
  · exact ⟨0, rfl, by omega⟩

private theorem ms_bind_ok {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {b : β}
    (h : (x >>= g) = .ok b) : ∃ a, x = .ok a ∧ g a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- `symUntil` only adds loads and stores. -/
theorem symUntil_le : ∀ (fuel o : Nat) (σ : Sym) (o' : Nat) (σ' : Sym) (mc : MCtl),
    symUntil t rs fuel o σ = .ok (o', σ', mc) → SymLe σ σ'
  | 0, _, _, _, _, _, h => by cases h
  | fuel + 1, o, σ, o', σ', mc, h => by
    obtain ⟨n, hn, -⟩ := ms_unitLen rs o
    simp only [symUntil, hn] at h
    obtain ⟨⟨σ1, c1⟩, hw, h⟩ := ms_bind_ok h
    have hle := symWords_le n o σ σ1 c1 hw
    dsimp only at h
    split at h
    · exact hle.trans (symUntil_le fuel _ σ1 o' σ' mc h)
    · cases h
      exact hle

/-- The words accepted by `symUntil` run as it says: the last word at `ol`, its end `o'`. -/
theorem symUntil_sound (hlink : linkCode base sym t rs = .ok code) (hsz : t.size ≤ 2 ^ 64)
    (hret : code retM = none) :
    ∀ (fuel o : Nat) (σ : Sym) (o' : Nat) (σ' : Sym) (mc : MCtl) (c : Ctx) (tm : MState),
      symUntil t rs fuel o σ = .ok (o', σ', mc) → c.sym = sym → Holds c σ tm →
      tm.pc = base + BitVec.ofNat 64 o → NoNil c σ' →
      ∃ tm' ol, o' = ol + 4 ∧ MStar H code retM tm tm' ∧ WordsPost c base ol σ' mc tm'
  | 0, _, _, _, _, _, _, _, h, _, _, _, _ => by cases h
  | fuel + 1, o, σ, o', σ', mc, c, tm, h, hsym, hH, hpc, hnil => by
    obtain ⟨n, hn, -⟩ := ms_unitLen rs o
    simp only [symUntil, hn] at h
    obtain ⟨⟨σ1, c1⟩, hw, h⟩ := ms_bind_ok h
    dsimp only at h
    split at h
    · rename_i hc1
      have hc1 : c1 = .fall := by simpa using hc1
      subst hc1
      have hle := symUntil_le fuel _ σ1 o' σ' mc h
      obtain ⟨tm1, hs1, hc, hx, hp⟩ :=
        symWords_sound (H := H) hlink hsz hret n o σ σ1 .fall c tm hw hsym hH hpc (hnil.mono hle)
      have hH1 : Holds c σ1 tm1 := ⟨hc, hx rfl⟩
      have hpc1 : tm1.pc = base + BitVec.ofNat 64 (o + 4 * (n + 1)) := by
        simp only [CtlPc] at hp
        rw [hp, at_nat]
        congr 1
      obtain ⟨tm2, ol, he, hs2, hp2⟩ := symUntil_sound hlink hsz hret fuel _ σ1 o' σ' mc c tm1 h
        hsym hH1 hpc1 hnil
      exact ⟨tm2, ol, he, mstar_trans hs1 hs2, hp2⟩
    · cases h
      obtain ⟨tm1, hs1, hp⟩ :=
        symWords_sound (H := H) hlink hsz hret n o σ σ' mc c tm hw hsym hH hpc hnil
      exact ⟨tm1, o + 4 * n, by omega, hs1, hp⟩

end Words

/-! ## Memory -/

private theorem ms_readMem_congr {M M' : Memory} : ∀ (n : Nat) (a : BitVec 64),
    (∀ j, j < n → M (a + BitVec.ofNat 64 j) = M' (a + BitVec.ofNat 64 j)) →
    readMem M a n = readMem M' a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    simp only [readMem]
    have ih := ms_readMem_congr n (a + 1) (fun j hj => by
      simpa only [GoFV.Proof.Gen.addr_succ] using h (j + 1) (by omega))
    rw [ih, h0]

/-- `n ≤ 8` bytes written, read back. -/
private theorem ms_readMem_self (mm : Memory) (A : BitVec 64) {n : Nat} (hn : n ≤ 8)
    (V : BitVec (8 * n)) : readMem (writeMem mm A n V) A n = V := by
  apply BitVec.eq_of_toNat_eq
  apply GoFV.Proof.Gen.readMem_of_bytes _ n A V.toNat
    (by have := V.isLt; rwa [Nat.pow_mul] at this)
  intro j hj
  rw [GoFV.Proof.Gen.writeMem_at n mm A V j hj hn]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ (8 * j) = 256 ^ j by rw [Nat.pow_mul], show 2 ^ 8 = 256 from rfl]

private theorem ms_toNat_add {a : BitVec 64} {k : Nat} (h : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt h

theorem TailSlot.addr_eval (c : Ctx) (s : TailSlot) :
    s.addr.eval c = c.s.sp + BitVec.ofNat 64 s.off := by
  simp [TailSlot.addr, Ex.eval_mkAdd, Ex.eval]

/-- The spills leave the memory outside their slots alone. -/
theorem storesMem_slots_out (c : Ctx) : ∀ (sl : List TailSlot) (m : Memory) (a : BitVec 64),
    (∀ s ∈ sl, c.s.sp.toNat + s.off + s.n ≤ 2 ^ 64) → ¬ InSlots sl c.s.sp a →
    storesMem c (sl.map TailSlot.store) m a = m a
  | [], _, _, _, _ => rfl
  | s :: sl, m, a, hw, ha => by
    simp only [List.map_cons, TailSlot.store, storesMem]
    rw [storesMem_slots_out c sl _ a (fun s' hs' => hw s' (List.mem_cons_of_mem _ hs'))
      (fun ⟨s', hs', h⟩ => ha ⟨s', List.mem_cons_of_mem _ hs', h⟩)]
    apply GoFV.Proof.Gen.writeMem_other
    intro j hj he
    have hws := hw s (List.mem_cons_self ..)
    rw [TailSlot.addr_eval] at he
    have e1 := congrArg BitVec.toNat he
    rw [ms_toNat_add (k := j) (by rw [ms_toNat_add (by omega)]; omega),
      ms_toNat_add (by omega)] at e1
    exact ha ⟨s, List.mem_cons_self .., by omega, by omega⟩

/-- After the spills, a slot holds its register's low bytes. -/
theorem storesMem_slot (c : Ctx) : ∀ (sl : List TailSlot) (m : Memory),
    slotsApart sl = true → (∀ s ∈ sl, c.s.sp.toNat + s.off + s.n ≤ 2 ^ 64 ∧ s.n ≤ 8) →
    ∀ s ∈ sl, readMem (storesMem c (sl.map TailSlot.store) m) (c.s.sp + BitVec.ofNat 64 s.off) s.n =
      (c.s.x (BitVec.ofNat 5 s.reg)).setWidth (8 * s.n)
  | [], _, _, _, _, hs => by cases hs
  | s0 :: sl, m, hap, hw, s, hs => by
    simp only [slotsApart, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at hap
    have hw' : ∀ s ∈ sl, c.s.sp.toNat + s.off + s.n ≤ 2 ^ 64 ∧ s.n ≤ 8 :=
      fun s' hs' => hw s' (List.mem_cons_of_mem _ hs')
    simp only [List.map_cons, TailSlot.store, storesMem]
    rcases List.mem_cons.1 hs with rfl | hs
    · have hw0 := hw s (List.mem_cons_self ..)
      have hout : ∀ j, j < s.n →
          ¬ InSlots sl c.s.sp (c.s.sp + BitVec.ofNat 64 s.off + BitVec.ofNat 64 j) := by
        rintro j hj ⟨s', hs', h1, h2⟩
        rw [ms_toNat_add (by rw [ms_toNat_add (by omega)]; omega), ms_toNat_add (by omega)]
          at h1 h2
        have := hap.1 s' hs'
        omega
      rw [TailSlot.addr_eval, ms_readMem_congr s.n _ (fun j hj => storesMem_slots_out c sl _ _
        (fun s' hs' => (hw' s' hs').1) (hout j hj)), ms_readMem_self _ _ hw0.2]
      rfl
    · exact storesMem_slot c sl _ hap.2 hw' s hs

/-! ## Reloads -/

private theorem ms_sext_bit (w : Nat) (hw : 0 < w ∧ w ≤ 64) (y : BitVec 64) (i : Nat) (hi : i < 64) :
    (GoFV.SSA.Sem.Arm64.sext w y).getLsbD i = if i < w then y.getLsbD i else y.getLsbD (w - 1) := by
  simp only [GoFV.SSA.Sem.Arm64.sext, show w ≠ 0 by omega, ↓reduceIte, BitVec.getLsbD_sshiftRight,
    BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
    GoFV.SSA.Sem.Arm64.mask, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases hiw : i < w
  · have e : 64 - w + i - (64 - w) = i := by omega
    have h1 : 64 - w + i < 64 := by omega
    have h2 : ¬ 64 - w + i < 64 - w := by omega
    have h3 : ¬ 64 ≤ i := by omega
    simp [hiw, e, h1, h2, h3, BitVec.getLsbD_eq_getElem hi]
    intro; exact hi
  · have h1 : ¬ 64 - w + i < 64 := by omega
    have h2 : ¬ 63 < 64 - w := by omega
    have h3 : ¬ 64 ≤ i := by omega
    have h4 : w - 1 < 64 := by omega
    have h5 : w - 1 < w := by omega
    have e : 63 - (64 - w) = w - 1 := by omega
    simp [hiw, e, h1, h2, h3, h4, h5]

/-- A reload keeps the slot's low bytes. -/
theorem reloadVal_low {n : Nat} (hn0 : 0 < n) (hn : n ≤ 8) (sg : Bool) (v : BitVec 64) :
    (reloadVal n sg v).setWidth (8 * n) = v.setWidth (8 * n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi64 : i < 64 := by omega
  cases sg
  · simp [reloadVal, hi, hi64]
  · simp only [reloadVal, ↓reduceIte, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
    rw [ms_sext_bit _ ⟨by omega, by omega⟩ _ _ hi64]
    simp [hi, hi64]

theorem reloadVal_congr {n : Nat} {sg : Bool} {v w : BitVec 64}
    (h : v.setWidth (8 * n) = w.setWidth (8 * n)) : reloadVal n sg v = reloadVal n sg w := by
  simp only [reloadVal, h]

theorem reloadVal_idem {n : Nat} (hn0 : 0 < n) (hn : n ≤ 8) (sg : Bool) (v : BitVec 64) :
    reloadVal n sg (reloadVal n sg v) = reloadVal n sg v :=
  reloadVal_congr (reloadVal_low hn0 hn sg v)

theorem reloadVal_eight (sg : Bool) (v : BitVec 64) : reloadVal 8 sg v = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases sg
  · simp [reloadVal]
  · simp only [reloadVal, ↓reduceIte]
    rw [ms_sext_bit _ ⟨by omega, by omega⟩ _ _ hi]
    simp [hi]

theorem reloadVal_bool {n : Nat} (hn0 : 0 < n) (hn : n ≤ 8) (sg b : Bool) :
    reloadVal n sg (if b then 1 else 0) = if b then 1 else 0 := by
  rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases sg <;> cases b <;> decide

open GoFV.SSA.Sem in
/-- A `runLoc` value that fits the `n` bytes of a slot: an integer of at most `8 n` bits, a
boolean, or (when `n = 8`) any other value. -/
def ValFits (v : Val) (n : Nat) : Prop :=
  match v with
  | .int w _ => w.bits ≤ 8 * n
  | .bool _ | .poison => True
  | _ => n = 8

open GoFV.SSA.Sem in
/-- The value relation survives a reload of a slot the value fits. -/
theorem valRel_reloadVal {ι : Blk → Option (BitVec 64)} {v : Val} {x : BitVec 64} {n : Nat}
    (sg : Bool) (hn0 : 0 < n) (hn : n ≤ 8) (h : ValRel ι v x) (hf : ValFits v n) :
    ValRel ι v (reloadVal n sg x) := by
  cases v with
  | int w y =>
    simp only [ValFits] at hf
    cases w with
    | w64 =>
      rw [show n = 8 by have : 64 ≤ 8 * n := hf; omega, reloadVal_eight]
      exact h
    | _ =>
      simp only [ValRel] at h ⊢
      rw [← h, ← BitVec.setWidth_setWidth_of_le _ (show _ ≤ 8 * n by simpa using hf),
        reloadVal_low hn0 hn, BitVec.setWidth_setWidth_of_le _ (show _ ≤ 8 * n by simpa using hf)]
  | bool b =>
    simp only [ValRel] at h ⊢
    rw [h, reloadVal_bool hn0 hn]
  | poison => trivial
  | ptr p =>
    simp only [ValFits] at hf
    rw [hf, reloadVal_eight]
    exact h
  | mem m => cases h
  | tuple vs => cases h
  | agg vs => cases h
  | _ => cases h

/-! ## The stack check -/

section Run

variable {base : BitVec 64} {sym : Nat → BitVec 64} {t : ByteArray} {rs : List Reloc}
  {code : Code} {H : Hooks} {retM : BitVec 64}

private theorem ms_holds_init (c : Ctx) : Holds c {} c.s where
  x _ _ := by simp [Sym.getX, Ex.eval]
  x31 := rfl
  sp := rfl
  nzcv := rfl
  v := rfl
  mem := rfl
  x30 := by simp [Sym.getX, Ex.eval]

private theorem ms_cmp {k : Reg} (hk : k.toNat < 30) (h27 : k ≠ 27) : k.toNat ∈ cmpRegs := by
  have : k.toNat ≠ 27 := by bv_omega
  simp [cmpRegs]
  omega

/-- A register that `σ` leaves alone keeps its value (`X30` given separately). -/
private theorem ms_reg {c : Ctx} {σ : Sym} {t : MState} (h : HoldsCore c σ t) {k : Reg}
    (h27 : k ≠ 27) (h30 : k ≠ 30 ∨ t.x 30 = c.s.x 30)
    (hσ : k.toNat < 30 → k.toNat ∈ cmpRegs → σ.getX k.toNat = .x k.toNat) : t.x k = c.s.x k := by
  by_cases e30 : k = 30
  · subst e30
    rcases h30 with h30 | h30
    · exact absurd rfl h30
    · exact h30
  by_cases e31 : k = 31
  · subst e31
    exact h.x31
  have hk : k.toNat < 30 := by bv_omega
  have e := h.x k.toNat hk
  rw [hσ hk (ms_cmp hk h27)] at e
  simpa [Ex.eval] using e

private theorem ms_ls (x y : BitVec 64) :
    GoFV.SSA.Sem.Cond.holds (condOf 9) (addSub true true x y).2 = decide (x.toNat ≤ y.toNat) := by
  rw [show condOf 9 = .ls from rfl]
  have hy := y.isLt
  have hx := x.isLt
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [h64] at hx hy
  simp only [GoFV.SSA.Sem.Cond.holds, GoFV.SSA.Sem.Cond.eval, addSub, sizedF, ↓reduceIte,
    GoFV.SSA.Sem.addWithCarry, BitVec.setWidth_eq]
  simp
  rw [Bool.eq_iff_iff]
  simp [BitVec.toNat_eq]
  omega

private theorem ms_at {base : BitVec 64} {o n e : Nat} (h : o + 4 * n + 4 = e) :
    at_ base ((o + 4 * n : Nat) + 4) = base + BitVec.ofNat 64 e := by
  rw [at_nat]
  congr 1
  omega

/-- The stack check: from the entry, `SP`, `R30`, the vector registers, the memory and every
register but `R16`, `R17` and `R27` unchanged, at its end when it passes, at the morestack tail
when it fails. -/
theorem stackCheck_run (hlink : linkCode base sym t rs = .ok code) (hsz : t.size ≤ 2 ^ 64)
    (hret : code retM = none) {az : Int} {gOff ce tail : Nat} {s0 : MState}
    (hc : checkStackCheck t rs az 0 gOff = .ok (ce, tail)) (hpc : s0.pc = base)
    (hg0 : 4096 ≤ (s0.x 28).toNat) (hg1 : (s0.x 28).toNat + 32 ≤ 2 ^ 64) (hgo : gOff ≤ 24) :
    ∃ sA, MStar H code retM s0 sA ∧
      sA.pc = base + BitVec.ofNat 64 (if CheckPasses az gOff s0 then ce else tail) ∧
      sA.sp = s0.sp ∧ (∀ k : Reg, k ≠ 16 → k ≠ 17 → k ≠ 27 → sA.x k = s0.x k) ∧ sA.v = s0.v ∧
      sA.mem = s0.mem := by
  obtain ⟨-, σ, hw, hce, hst, hsp, hx30, hld, hregs⟩ := checkStackCheck_spec hc
  obtain ⟨n, hn⟩ : ∃ n, (if az ≤ 128 then 3 else 4) = n + 1 := by
    split
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  rw [hn] at hw hce
  have hnil : NoNil ⟨s0, sym⟩ σ := by
    refine ⟨fun a m ham => ?_, fun a m v hv => by simp [hst] at hv⟩
    rw [hld] at ham
    simp only [List.mem_singleton, Prod.mk.injEq] at ham
    obtain ⟨rfl, rfl⟩ := ham
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    simp only [Ex.eval_mkAdd, Ex.eval, nilPage, decide_eq_false_iff_not, Nat.not_lt]
    show 4096 ≤ (s0.x 28 + BitVec.ofNat 64 gOff).toNat
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h64] at hg1 ⊢
    omega
  obtain ⟨tm, hrun, hcore, hx, hctl⟩ := symWords_sound (H := H) hlink hsz hret n 0 {} σ _
    ⟨s0, sym⟩ s0 hw rfl (ms_holds_init _) (by simp [hpc]) hnil
  have hls : GoFV.SSA.Sem.Cond.holds (condOf 9) (Fl.eval ⟨s0, sym⟩ (.addSub true true
      (if az ≤ 128 then Ex.sp else Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-(az - 128)))))
      (.ld 8 (Ex.mkAdd (.x 28) (.k (BitVec.ofNat 64 gOff)))))) =
      !decide (CheckPasses az gOff s0) := by
    simp only [Fl.eval]
    rw [ms_ls]
    unfold CheckPasses
    by_cases ha : az ≤ 128
    · simp only [ha, ↓reduceIte]
      simp [Ex.eval, Ex.eval_mkAdd, ← Nat.not_lt]
    · simp only [ha, ↓reduceIte]
      simp [Ex.eval, Ex.eval_mkAdd, ← Nat.not_lt]
  simp only [CtlPc, hls] at hctl
  have h30 : tm.x 30 = s0.x 30 := by
    rw [hx rfl, hx30]
    rfl
  refine ⟨tm, hrun, ?_, ?_, fun k h16 h17 h27 => ?_, hcore.v, ?_⟩
  · rw [hctl]
    by_cases hp : CheckPasses az gOff s0
    · simp only [hp, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [hce]
      exact ms_at (by omega)
    · simp only [hp, decide_false, Bool.not_false, ↓reduceIte]
      rw [at_nat]
  · rw [hcore.sp, hsp]
    rfl
  · refine ms_reg hcore h27 (Or.inr h30) fun hk hm => hregs _ hm ?_ ?_
    · bv_omega
    · bv_omega
  · rw [hcore.mem, hst]
    rfl

theorem reloadOf_mem {sl : List TailSlot} {r : Nat} {q : TailSlot} (h : reloadOf sl r = some q) :
    q ∈ sl ∧ q.reg = r := by
  unfold reloadOf at h
  exact ⟨List.mem_reverse.1 (List.mem_of_find?_eq_some h), by simpa using List.find?_some h⟩

theorem TailSlot.reload_eval {c : Ctx} {q : TailSlot} {v : BitVec 64}
    (h : readMem c.s.mem (c.s.sp + BitVec.ofNat 64 q.off) q.n = v.setWidth (8 * q.n)) :
    q.reload.eval c = reloadVal q.n q.sg v := by
  unfold TailSlot.reload reloadVal
  cases q.sg <;> simp [Ex.eval_mkSext, Ex.eval, TailSlot.addr_eval, h]

/-- The memory `M'` agrees with `M` on the 32 bytes at `g`: so do the words there. -/
private theorem ms_word32 {M M' : Memory} {g : BitVec 64} {k : Nat} (hk : k ≤ 24)
    (h : ∀ j, j < 32 → M' (g + BitVec.ofNat 64 j) = M (g + BitVec.ofNat 64 j)) :
    readMem M' (g + BitVec.ofNat 64 k) 8 = readMem M (g + BitVec.ofNat 64 k) 8 :=
  ms_readMem_congr 8 _ fun j hj => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact h (k + j) (by omega)

/-- One round trip through the morestack tail from the entry `u` whose stack check fails: back at
the entry with `SP`, `R26`, `R28`, `R29`, `R30` kept, the spilled registers reloaded, the memory
kept but the slots and the guard word, the guard lower. -/
private theorem more_round (hlink : linkCode base sym t rs = .ok code) (hsz : t.size ≤ 2 ^ 64)
    (hret : code retM = none) {az : Int} {gOff ce tail e : Nat} {spills : List Spill}
    {sl : List TailSlot} {s0 u : MState}
    (hc : checkStackCheck t rs az 0 gOff = .ok (ce, tail)) (hgo : gOff = 16 ∨ gOff = 24)
    (htl : checkTail t rs spills 0 tail = .ok e) (hpl : tailPlan spills = .ok sl)
    (hms : ∀ n add, tailCall t rs tail = some (n, add) →
      MorestackOK H code retM (sym n + BitVec.ofInt 64 add) az gOff s0)
    (hsep : TailSep spills s0) (hspn : 4096 ≤ s0.sp.toNat)
    (hg0 : 4096 ≤ (s0.x 28).toNat) (hg1 : (s0.x 28).toNat + 32 ≤ 2 ^ 64)
    (hpc : u.pc = base) (hsp : u.sp = s0.sp) (h28 : u.x 28 = s0.x 28)
    (hlo : u.word (u.x 28) = s0.word (s0.x 28)) (hfail : ¬ CheckPasses az gOff u) :
    ∃ u', MStar H code retM u u' ∧ u'.pc = base ∧ u'.sp = u.sp ∧ u'.x 26 = u.x 26 ∧
      u'.x 28 = u.x 28 ∧ u'.x 29 = u.x 29 ∧ u'.x 30 = u.x 30 ∧
      (∀ (k : Reg) (q : TailSlot), reloadOf sl k.toNat = some q →
        u'.x k = reloadVal q.n q.sg (u.x k)) ∧
      (∀ a, ¬ InSlots sl u.sp a → ¬ InWord (u.x 28 + BitVec.ofNat 64 gOff) a →
        u'.mem a = u.mem a) ∧
      guardOf gOff u' < guardOf gOff u := by
  obtain ⟨sl', hpl', o1, σ1, n, add, hu1, hst1, hsp1, hld1, hx1, o2, σ2, hu2, hst2, hsp2, h302,
    hld2, hx2⟩ := checkTail_spec htl
  rw [hpl] at hpl'
  cases hpl'
  obtain ⟨hap, hslot⟩ := tailPlan_spec hpl
  have hsep' := hsep sl hpl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  -- the check fails: the words reach the tail
  obtain ⟨tA, hrA, hpcA, hspA, hxA, -, hmA⟩ := stackCheck_run (H := H) hlink hsz hret hc hpc
    (by rw [h28]; exact hg0) (by rw [h28]; exact hg1) (by omega)
  simp only [hfail, ↓reduceIte] at hpcA
  have hspA0 : tA.sp = s0.sp := by rw [hspA, hsp]
  have hgA : tA.x 28 = s0.x 28 := by rw [hxA 28 (by decide) (by decide) (by decide), h28]
  -- a slot's address is above the nil page
  have hslotA : ∀ (c : Ctx), c.s.sp = s0.sp → ∀ s ∈ sl, nilPage (s.addr.eval c) = false := by
    intro c hcs s hs
    have := hsep' s hs
    have := hslot s hs
    rw [TailSlot.addr_eval, hcs]
    simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
    rw [ms_toNat_add (by omega)]
    omega
  -- the spills, `MOVD R30, R3` and the call
  have hnil1 : NoNil ⟨tA, sym⟩ σ1 := by
    refine ⟨fun a m h => by simp [hld1] at h, fun a m v h => ?_⟩
    rw [hst1] at h
    obtain ⟨s, hs, he⟩ := List.mem_map.1 h
    simp only [TailSlot.store, Prod.mk.injEq] at he
    rw [← he.1]
    exact hslotA _ hspA0 s hs
  obtain ⟨t1, ol1, ho1, hr1, hc1, -, hctl1⟩ := symUntil_sound (H := H) hlink hsz hret _ tail {}
    o1 σ1 (.call n add) ⟨tA, sym⟩ tA hu1 rfl (ms_holds_init _) hpcA hnil1
  simp only [CtlPc] at hctl1
  obtain ⟨hpc1, hlr1⟩ := hctl1
  have hsp1' : t1.sp = tA.sp := by rw [hc1.sp, hsp1]; rfl
  have hx1' : ∀ k : Nat, k < 30 → k ∈ cmpRegs → k ≠ 3 →
      t1.x (BitVec.ofNat 5 k) = tA.x (BitVec.ofNat 5 k) := by
    intro k hk hm h3
    rw [hc1.x k hk, hx1 k hm]
    simp only [h3, ↓reduceIte]
    rfl
  have h3' : t1.x 3 = tA.x 30 := by
    have := hc1.x 3 (by omega)
    rw [hx1 3 (by decide)] at this
    exact this
  have hm1 : t1.mem = storesMem ⟨tA, sym⟩ (sl.map TailSlot.store) tA.mem := by
    rw [hc1.mem, hst1]
  have hw' : ∀ s ∈ sl, (⟨tA, sym⟩ : Ctx).s.sp.toNat + s.off + s.n ≤ 2 ^ 64 := by
    intro s hs
    show tA.sp.toNat + _ + _ ≤ _
    rw [hspA0]
    exact (hsep' s hs).1
  -- `g`'s 32 bytes are no slot's
  have hg32 : ∀ j, j < 32 → t1.mem (s0.x 28 + BitVec.ofNat 64 j) = u.mem (s0.x 28 + BitVec.ofNat 64 j) := by
    intro j hj
    rw [hm1, storesMem_slots_out _ _ _ _ hw', hmA]
    rintro ⟨s, hs, h1, h2⟩
    have := hsep' s hs
    simp only at h1 h2
    rw [hspA0, ms_toNat_add (by omega)] at h1 h2
    omega
  have hg28 : t1.x 28 = s0.x 28 :=
    (hx1' 28 (by omega) (by decide) (by decide)).trans hgA
  have hgw : ∀ k, k ≤ 24 → readMem t1.mem (t1.x 28 + BitVec.ofNat 64 k) 8 =
      readMem u.mem (u.x 28 + BitVec.ofNat 64 k) 8 := by
    intro k hk
    rw [hg28, h28]
    exact ms_word32 hk hg32
  -- the hook
  have htc : tailCall t rs tail = some (n, add) := by simp [tailCall, hu1]
  obtain ⟨hcode, hne, hhook⟩ := hms n add htc
  have hfail1 : ¬ CheckPasses az gOff t1 := by
    unfold CheckPasses at hfail ⊢
    rw [hgw gOff (by omega), hsp1', hspA]
    exact hfail
  have hlo1 : t1.word (t1.x 28) = s0.word (s0.x 28) := by
    have h0 : readMem t1.mem (t1.x 28) 8 = readMem u.mem (u.x 28) 8 := by
      simpa using hgw 0 (by omega)
    rw [← hlo]
    unfold MState.word
    rw [h0]
  obtain ⟨t2, hcall, hpc2, hsp2', h262, h282, h292, h302', hmem2, hgd⟩ := hhook t1 hpc1
    (by rw [hsp1', hspA0]) hg28 hlo1 hfail1
  have hs2 : MStep H code retM t1 t2 :=
    .hook (by rw [hpc1]; exact hne) (by rw [hpc1]; exact hcode) hcall
  -- the reloads and the jump back
  have hpc2' : t2.pc = base + BitVec.ofNat 64 o1 := by
    rw [hpc2, hlr1, ho1, at_nat]
    congr 1
  have hsp2A : t2.sp = tA.sp := by rw [hsp2', hsp1']
  have hnil2 : NoNil ⟨t2, sym⟩ σ2 := by
    refine ⟨fun a m h => ?_, fun a m v h => by simp [hst2] at h⟩
    obtain ⟨s, hs, h1, -⟩ := hld2 (a, m) h
    simp only at h1
    rw [← h1]
    exact hslotA ⟨t2, sym⟩ (by rw [hsp2A, hspA0]) s hs
  obtain ⟨t3, ol2, -, hr3, hc3, hx3, hctl3⟩ := symUntil_sound (H := H) hlink hsz hret _ o1 {}
    o2 σ2 (.jmp ((0 : Nat) : Int)) ⟨t2, sym⟩ t2 hu2 rfl (ms_holds_init _) hpc2' hnil2
  simp only [CtlPc] at hctl3
  have hx3' : ∀ k : Nat, k < 30 → k ∈ cmpRegs →
      t3.x (BitVec.ofNat 5 k) = (((reloadOf sl k).map TailSlot.reload).getD (Ex.x k)).eval ⟨t2, sym⟩ := by
    intro k hk hm
    rw [hc3.x k hk, hx2 k hm]
  have hnone : ∀ k, 16 ≤ k → reloadOf sl k = none := by
    intro k hk
    cases hq : reloadOf sl k with
    | none => rfl
    | some q =>
      obtain ⟨hq1, hq2⟩ := reloadOf_mem hq
      have := (hslot q hq1).1
      omega
  have hkeep : ∀ k : Nat, 16 ≤ k → k < 30 → k ∈ cmpRegs →
      t3.x (BitVec.ofNat 5 k) = t2.x (BitVec.ofNat 5 k) := by
    intro k h16 hk hm
    rw [hx3' k hk hm, hnone k h16]
    rfl
  have hsp3 : t3.sp = t2.sp := by rw [hc3.sp, hsp2]; rfl
  have hm3 : t3.mem = t2.mem := by rw [hc3.mem, hst2]; rfl
  have h303 : t3.x 30 = t2.x 30 := by
    rw [hx3 rfl, h302]
    rfl
  have hk26 : t3.x 26 = u.x 26 :=
    (hkeep 26 (by omega) (by omega) (by decide)).trans (h262.trans
      ((hx1' 26 (by omega) (by decide) (by decide)).trans (hxA 26 (by decide) (by decide) (by decide))))
  have hk28 : t3.x 28 = u.x 28 :=
    (hkeep 28 (by omega) (by omega) (by decide)).trans (h282.trans (hg28.trans h28.symm))
  have hk29 : t3.x 29 = u.x 29 :=
    (hkeep 29 (by omega) (by omega) (by decide)).trans (h292.trans
      ((hx1' 29 (by omega) (by decide) (by decide)).trans (hxA 29 (by decide) (by decide) (by decide))))
  -- a slot's bytes are not the guard word's
  have hslotG : ∀ q ∈ sl, ∀ j, j < q.n →
      ¬ InWord (t1.x 28 + BitVec.ofNat 64 gOff) (t2.sp + BitVec.ofNat 64 q.off + BitVec.ofNat 64 j) := by
    intro q hq j hj ⟨h1, h2⟩
    have := hsep' q hq
    have := hslot q hq
    have e1 : (s0.x 28 + BitVec.ofNat 64 gOff).toNat = (s0.x 28).toNat + gOff :=
      ms_toNat_add (by omega)
    have e2 : (t2.sp + BitVec.ofNat 64 q.off + BitVec.ofNat 64 j).toNat = s0.sp.toNat + q.off + j := by
      rw [hsp2A, hspA0, ms_toNat_add (by rw [ms_toNat_add (by omega)]; omega),
        ms_toNat_add (by omega)]
    rw [hg28, e1, e2] at h1 h2
    omega
  refine ⟨t3, mstar_trans hrA (mstar_trans hr1 (mstar_trans (mstar_single hs2) hr3)), ?_,
    by rw [hsp3, hsp2A, hspA], hk26, hk28, hk29, by rw [h303, h302', h3', hxA 30 (by decide)
      (by decide) (by decide)], fun k q hkq => ?_, fun a ha hw => ?_, ?_⟩
  · rw [hctl3]
    simp [at_]
  · obtain ⟨hq, hreg⟩ := reloadOf_mem hkq
    have hq16 := (hslot q hq).1
    have hk : k.toNat < 30 := by omega
    have hkm : k.toNat ∈ cmpRegs := by simp [cmpRegs]; omega
    have e := hx3' k.toNat hk hkm
    rw [show BitVec.ofNat 5 k.toNat = k by simp, hkq] at e
    rw [e]
    apply TailSlot.reload_eval
    show readMem t2.mem (t2.sp + BitVec.ofNat 64 q.off) q.n = _
    rw [ms_readMem_congr q.n _ fun j hj => hmem2 _ (hslotG q hq j hj)]
    have := storesMem_slot ⟨tA, sym⟩ sl tA.mem hap (fun s hs => ⟨hw' s hs, (hslot s hs).2.2⟩) q hq
    rw [← hm1, ← hsp2A] at this
    rw [this]
    show (tA.x (BitVec.ofNat 5 q.reg)).setWidth _ = _
    rw [hreg, show BitVec.ofNat 5 k.toNat = k by simp, hxA k (by bv_omega) (by bv_omega)
      (by bv_omega)]
  · rw [hm3, hmem2 a (by rw [hg28, ← h28]; exact hw), hm1,
      storesMem_slots_out _ _ _ _ hw' (by rw [show (⟨tA, sym⟩ : Ctx).s.sp = u.sp from hspA]; exact ha),
      hmA]
  · unfold guardOf at hgd ⊢
    rw [hgw gOff (by omega), h282, hg28, ← h28] at hgd
    rw [hm3, hk28]
    exact hgd

theorem MoreStep.refl (sl : List TailSlot) (gOff : Nat) (s0 : MState) : MoreStep sl gOff s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => Or.inl rfl, fun _ _ _ => rfl⟩

/-- **The morestack loop.** From the entry `s0` of a function whose stack check (at `0`, ending
at `ce`, its tail at `tail`, reading `gOff(g)`) and morestack tail `checkObj` accepted, under
`runtime.morestack`'s contract (`MorestackOK`) and with the spill slots apart from `g`
(`TailSep`), the machine runs (zero or more round trips through the tail) to a state at the
entry whose stack check passes, `s0` but for the reloaded registers, the other registers but
`R26`, `R28`–`R30`, the slots and the guard word (`MoreStep`). -/
theorem more_loop (hlink : linkCode base sym t rs = .ok code) (hsz : t.size ≤ 2 ^ 64)
    (hret : code retM = none) {az : Int} {gOff ce tail e : Nat} {spills : List Spill}
    {sl : List TailSlot} {s0 : MState}
    (hc : checkStackCheck t rs az 0 gOff = .ok (ce, tail)) (hgo : gOff = 16 ∨ gOff = 24)
    (htl : checkTail t rs spills 0 tail = .ok e) (hpl : tailPlan spills = .ok sl)
    (hms : ∀ n add, tailCall t rs tail = some (n, add) →
      MorestackOK H code retM (sym n + BitVec.ofInt 64 add) az gOff s0)
    (hsep : TailSep spills s0) (hspn : 4096 ≤ s0.sp.toNat)
    (hg0 : 4096 ≤ (s0.x 28).toNat) (hg1 : (s0.x 28).toNat + 32 ≤ 2 ^ 64) (hpc0 : s0.pc = base) :
    ∃ u, MStar H code retM s0 u ∧ MoreStep sl gOff s0 u ∧ CheckPasses az gOff u := by
  obtain ⟨-, hslot⟩ := tailPlan_spec hpl
  have hsep' := hsep sl hpl
  have step : ∀ u, MStar H code retM s0 u → MoreStep sl gOff s0 u → ¬ CheckPasses az gOff u →
      ∃ u', MStar H code retM s0 u' ∧ MoreStep sl gOff s0 u' ∧ guardOf gOff u' < guardOf gOff u := by
    intro u hs hm hfail
    have hlo : u.word (u.x 28) = s0.word (s0.x 28) := by
      unfold MState.word
      rw [hm.x28, ms_readMem_congr 8 _ fun j hj => hm.mem _ ?_ ?_]
      · rintro ⟨s, hs, h1, h2⟩
        have := hsep' s hs
        rw [ms_toNat_add (by omega)] at h1 h2
        omega
      · rintro ⟨h1, -⟩
        rw [ms_toNat_add (by omega), ms_toNat_add (by omega)] at h1
        omega
    obtain ⟨u', hr, hpc', hsp', h26', h28', h29', h30', hregs', hmem', hgd⟩ :=
      more_round (H := H) hlink hsz hret hc hgo htl hpl hms hsep hspn hg0 hg1
        (hm.pc.trans hpc0) hm.sp hm.x28 hlo hfail
    refine ⟨u', mstar_trans hs hr, ⟨hpc'.trans hpc0.symm, hsp'.trans hm.sp, h26'.trans hm.x26,
      h28'.trans hm.x28, h29'.trans hm.x29, h30'.trans hm.x30, fun k q hkq => Or.inr ?_,
      fun a ha hw => ?_⟩, hgd⟩
    · have hq := hslot q (reloadOf_mem hkq).1
      rw [hregs' k q hkq]
      rcases hm.regs k q hkq with h | h
      · rw [h]
      · rw [h, reloadVal_idem hq.2.1 hq.2.2]
    · rw [hmem' a (by rwa [hm.sp]) (by rwa [hm.x28]), hm.mem a ha hw]
  suffices h : ∀ N u, guardOf gOff u ≤ N → MStar H code retM s0 u → MoreStep sl gOff s0 u →
      ∃ u', MStar H code retM s0 u' ∧ MoreStep sl gOff s0 u' ∧ CheckPasses az gOff u' from
    h _ s0 (Nat.le_refl _) .refl (MoreStep.refl sl gOff s0)
  intro N
  induction N with
  | zero =>
    intro u hN hs hm
    by_cases hp : CheckPasses az gOff u
    · exact ⟨u, hs, hm, hp⟩
    · obtain ⟨u', -, -, hgd⟩ := step u hs hm hp
      omega
  | succ N ih =>
    intro u hN hs hm
    by_cases hp : CheckPasses az gOff u
    · exact ⟨u, hs, hm, hp⟩
    · obtain ⟨u', hs', hm', hgd⟩ := step u hs hm hp
      exact ih u' (by omega) hs' hm'


end Run

end GoFV.Proof.Obj
