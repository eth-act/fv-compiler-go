import GoFV.Proof.Obj.Words
import GoFV.Proof.Obj.Spec
import GoFV.Proof.Gen.Mem

/-!
# The prologue and the epilogue (`checkPrologue`, `retOK`; `docs/plans/proofs3.md` §2, row C6/D3)

`obj_entry`: from a call of the function (`MachEntry` at `base`), when the stack check passes
(`CheckPasses`: the limit above `stackguard0`), the prologue runs to the body's first offset. A
frameless function has no prologue (the state is the entry's); a framed one reaches a state
with the frame of `BodyEntry` (`SP` lowered by `autosize`, the caller's `LR` and `FP` saved,
`R29 = SP − 8`); registers but the stack check's (`R16`, `R17`), the large-frame scratch `R20`,
`R27` and `R29` are unchanged, and memory outside the two saved words.

`obj_exit`: from a state at the offset of a P0 `RET` (without operand), the epilogue pops the
frame (`SP` raised by `autosize`), restores `R29` (a leaf recomputes it, others reload it from
`-8(SP)`) and returns through `R30` (a non-leaf reloads it from `0(SP)` first).

Both run the template's words by `symWords_sound` from the empty effect and read the final
state off `HoldsCore`; the validator's facts are `checkStackCheck_spec`, `frameOK_spec`,
`checkPrologue_spec`, `checkBody_spec`, `checkOne_spec` and `retOK_spec`.
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.SSA.Sem (MStar)

/-- The stack check with frame size `az` reading `gOff(g)` passes from `s`: the limit (`SP`,
or `SP − (az − StackSmall)` above `StackSmall`) is above the guard, unsigned. -/
def CheckPasses (az : Int) (gOff : Nat) (s : MState) : Prop :=
  (readMem s.mem (s.x 28 + BitVec.ofNat 64 gOff) 8).toNat <
    (if az ≤ 128 then s.sp else s.sp + BitVec.ofInt 64 (-(az - 128))).toNat

/-! ## Registers, memory, arithmetic -/

private theorem fr_holds_init (c : Ctx) : Holds c {} c.s where
  x _ _ := by simp [Sym.getX, Ex.eval]
  x31 := rfl
  sp := rfl
  nzcv := rfl
  v := rfl
  mem := rfl
  x30 := by simp [Sym.getX, Ex.eval]

private theorem fr_cmp {k : Reg} (hk : k.toNat < 30) (h27 : k ≠ 27) : k.toNat ∈ cmpRegs := by
  have : k.toNat ≠ 27 := by bv_omega
  simp [cmpRegs]
  omega

/-- A register that `σ` leaves alone keeps its value (`X30` given separately). -/
private theorem fr_reg {c : Ctx} {σ : Sym} {t : MState} (h : HoldsCore c σ t) {k : Reg}
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
  rw [hσ hk (fr_cmp hk h27)] at e
  simpa [Ex.eval] using e

private theorem fr_readMem_congr {M M' : Memory} : ∀ (n : Nat) (a : BitVec 64),
    (∀ j, j < n → M (a + BitVec.ofNat 64 j) = M' (a + BitVec.ofNat 64 j)) →
    readMem M a n = readMem M' a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    simp only [readMem]
    have ih := fr_readMem_congr n (a + 1) (fun j hj => by
      simpa only [GoFV.Proof.Gen.addr_succ] using h (j + 1) (by omega))
    rw [ih, h0]

private theorem fr_readMem_self (mm : Memory) (A : BitVec 64) (V : BitVec (8 * 8)) :
    readMem (writeMem mm A 8 V) A 8 = V := by
  apply BitVec.eq_of_toNat_eq
  apply GoFV.Proof.Gen.readMem_of_bytes _ 8 A V.toNat (by have := V.isLt; simpa using this)
  intro j hj
  rw [GoFV.Proof.Gen.writeMem_at 8 mm A V j hj (Nat.le_refl 8)]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ (8 * j) = 256 ^ j by rw [Nat.pow_mul], show 2 ^ 8 = 256 from rfl]

private theorem fr_readMem_other (mm : Memory) (A B : BitVec 64) (V : BitVec (8 * 8))
    (hd : ∀ i j, i < 8 → j < 8 → B + BitVec.ofNat 64 i ≠ A + BitVec.ofNat 64 j) :
    readMem (writeMem mm A 8 V) B 8 = readMem mm B 8 :=
  fr_readMem_congr 8 B fun i hi =>
    GoFV.Proof.Gen.writeMem_other 8 mm A V _ fun j hj => hd i j hi hj

private theorem fr_word (v : BitVec 64) : ((v.setWidth (8 * 8)).cast (by omega) : BitVec 64) = v := by
  apply BitVec.eq_of_toNat_eq
  simp

private theorem fr_wordR (s : MState) (a : BitVec 64) : s.word a = readMem s.mem a 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [MState.word]

/-- The two saved words of the frame, stored in either order. -/
private theorem fr_frame_mem {c : Ctx} {az : Int} {A : BitVec 64} {st : List (Ex × Nat × Ex)}
    {s1 : MState} (hst : st = frameStores az ∨ st = (frameStores az).reverse)
    (h1 : (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az)))).eval c = A)
    (h2 : (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az - 8)))).eval c = A - 8)
    (hm : s1.mem = storesMem c st c.s.mem) :
    s1.word A = c.s.x 30 ∧ s1.word (A - 8) = c.s.x 29 ∧
      ∀ a, 16 ≤ (a - (A - 8)).toNat → s1.mem a = c.s.mem a := by
  have hd1 : ∀ i j, i < 8 → j < 8 → A + BitVec.ofNat 64 i ≠ A - 8 + BitVec.ofNat 64 j := by
    intro i j hi hj; bv_omega
  have hd2 : ∀ i j, i < 8 → j < 8 → A - 8 + BitVec.ofNat 64 i ≠ A + BitVec.ofNat 64 j := by
    intro i j hi hj; bv_omega
  have hout : ∀ a, 16 ≤ (a - (A - 8)).toNat → ∀ j, j < 8 →
      a ≠ A + BitVec.ofNat 64 j ∧ a ≠ A - 8 + BitVec.ofNat 64 j := by
    intro a ha j hj; constructor <;> bv_omega
  rcases hst with rfl | rfl
  · simp only [frameStores, storesMem, h1, h2] at hm
    refine ⟨?_, ?_, fun a ha => ?_⟩
    · simp only [MState.word, hm]
      rw [fr_readMem_other _ _ _ _ hd1, fr_readMem_self]
      exact fr_word _
    · simp only [MState.word, hm]
      rw [fr_readMem_self]
      exact fr_word _
    · rw [hm, GoFV.Proof.Gen.writeMem_other _ _ _ _ _ fun j hj => (hout a ha j hj).2,
        GoFV.Proof.Gen.writeMem_other _ _ _ _ _ fun j hj => (hout a ha j hj).1]
  · simp only [frameStores, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, storesMem, h1, h2] at hm
    refine ⟨?_, ?_, fun a ha => ?_⟩
    · simp only [MState.word, hm]
      rw [fr_readMem_self]
      exact fr_word _
    · simp only [MState.word, hm]
      rw [fr_readMem_other _ _ _ _ hd2, fr_readMem_self]
      exact fr_word _
    · rw [hm, GoFV.Proof.Gen.writeMem_other _ _ _ _ _ fun j hj => (hout a ha j hj).1,
        GoFV.Proof.Gen.writeMem_other _ _ _ _ _ fun j hj => (hout a ha j hj).2]

private theorem fr_m8 (s : BitVec 64) : s + BitVec.ofInt 64 (-8) = s - 8 := by
  rw [show BitVec.ofInt 64 (-8) = -8 from by decide, BitVec.sub_eq_add_neg]

private theorem fr_neg (s : BitVec 64) {az : Int} (h : 0 ≤ az) :
    s + BitVec.ofInt 64 (-az) = s - BitVec.ofNat 64 az.toNat := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [BitVec.ofInt_neg, BitVec.ofInt_natCast, BitVec.sub_eq_add_neg]
  simp

private theorem fr_neg8 (s : BitVec 64) {az : Int} (h : 0 ≤ az) :
    s + BitVec.ofInt 64 (-az - 8) = s - BitVec.ofNat 64 az.toNat - 8 := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, ← BitVec.add_assoc, fr_neg s h, fr_m8]

private theorem fr_ls {x y : BitVec 64} (h : y.toNat < x.toNat) :
    GoFV.SSA.Sem.Cond.holds (condOf 9) (addSub true true x y).2 = false := by
  rw [show condOf 9 = .ls from rfl]
  have hy := y.isLt
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [h64] at hy
  simp only [GoFV.SSA.Sem.Cond.holds, GoFV.SSA.Sem.Cond.eval, addSub, sizedF, ↓reduceIte,
    GoFV.SSA.Sem.addWithCarry, BitVec.setWidth_eq]
  simp
  refine ⟨by omega, fun e => ?_⟩
  have := congrArg BitVec.toNat e
  simp at this
  omega

private theorem fr_at {base : BitVec 64} {o n e : Nat} (h : o + 4 * n + 4 = e) :
    at_ base ((o + 4 * n : Nat) + 4) = base + BitVec.ofNat 64 e := by
  rw [at_nat]
  congr 1
  omega

/-! ## The stack check and the frame -/

section Run

variable {base : BitVec 64} {sym : Nat → BitVec 64} {t : ByteArray} {rs : List Reloc}
  {code : Code} {H : Hooks} {retM : BitVec 64}

/-- The stack check, when it passes, falls through to its end with `SP`, the vector registers,
the memory and every register but `R16`, `R17` and `R27` unchanged. -/
private theorem check_run (hlink : linkCode base sym t rs = .ok code) (hsz : t.size ≤ 2 ^ 64)
    (hret : code retM = none) {az : Int} {gOff ce tail : Nat} {s0 : MState}
    (hc : checkStackCheck t rs az 0 gOff = .ok (ce, tail)) (hpc : s0.pc = base)
    (hg0 : 4096 ≤ (s0.x 28).toNat) (hg1 : (s0.x 28).toNat + 32 ≤ 2 ^ 64) (hgo : gOff ≤ 24)
    (hpass : CheckPasses az gOff s0) :
    ∃ sA, MStar H code retM s0 sA ∧ sA.pc = base + BitVec.ofNat 64 ce ∧ sA.sp = s0.sp ∧
      (∀ k : Reg, k ≠ 16 → k ≠ 17 → k ≠ 27 → sA.x k = s0.x k) ∧ sA.v = s0.v ∧
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
    ⟨s0, sym⟩ s0 hw rfl (fr_holds_init _) (by simp [hpc]) hnil
  have hls : GoFV.SSA.Sem.Cond.holds (condOf 9) (Fl.eval ⟨s0, sym⟩ (.addSub true true
      (if az ≤ 128 then Ex.sp else Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-(az - 128)))))
      (.ld 8 (Ex.mkAdd (.x 28) (.k (BitVec.ofNat 64 gOff)))))) = false := by
    simp only [Fl.eval]
    apply fr_ls
    unfold CheckPasses at hpass
    have e : ∀ m : BitVec (8 * 8), (m.setWidth 64).toNat = m.toNat := fun m => by simp
    by_cases ha : az ≤ 128
    · simp only [ha, ↓reduceIte] at hpass ⊢
      simpa [Ex.eval, Ex.eval_mkAdd, e] using hpass
    · simp only [ha, ↓reduceIte] at hpass ⊢
      simpa [Ex.eval, Ex.eval_mkAdd, e] using hpass
  simp only [CtlPc, hls, Bool.false_eq_true, ↓reduceIte] at hctl
  have h30 : tm.x 30 = s0.x 30 := by
    rw [hx (fun _ _ h => by cases h), hx30]
    rfl
  refine ⟨tm, hrun, ?_, ?_, fun k h16 h17 h27 => ?_, hcore.v, ?_⟩
  · rw [hctl, hce]
    exact fr_at (by omega)
  · rw [hcore.sp, hsp]
    rfl
  · refine fr_reg hcore h27 (Or.inr h30) fun hk hm => hregs _ hm ?_ ?_
    · bv_omega
    · bv_omega
  · rw [hcore.mem, hst]
    rfl

/-- The frame words: `SP` lowered by `az`, the `LR` and `FP` of `sA` saved at `0(SP)` and
`-8(SP)`, `R29 = SP - 8`; every register but `R20`, `R27` and `R29`, the vector registers and the
memory outside the two words unchanged. -/
private theorem frame_run (hlink : linkCode base sym t rs = .ok code) (hsz : t.size ≤ 2 ^ 64)
    (hret : code retM = none) {az : Int} {fo body : Nat} {σ : Sym} {sA : MState}
    (hw : symWords t rs ((body - fo) / 4) fo {} = .ok (σ, .fall)) (hf : frameOK az σ = .ok ())
    (hfo : fo < body) (hmod : (body - fo) % 4 = 0) (hpc : sA.pc = base + BitVec.ofNat 64 fo)
    (haz : 0 ≤ az) (hsp : 4096 + az + 8 ≤ (sA.sp.toNat : Int)) :
    ∃ s1, MStar H code retM sA s1 ∧ s1.pc = base + BitVec.ofNat 64 body ∧
      s1.sp = sA.sp - BitVec.ofNat 64 az.toNat ∧ s1.word s1.sp = sA.x 30 ∧
      s1.word (s1.sp - 8) = sA.x 29 ∧ s1.x 29 = s1.sp - 8 ∧
      (∀ k : Reg, k ≠ 20 → k ≠ 27 → k ≠ 29 → s1.x k = sA.x k) ∧ s1.v = sA.v ∧
      (∀ a, 16 ≤ (a - (s1.sp - 8)).toNat → s1.mem a = sA.mem a) := by
  obtain ⟨hsp', h29, hregs, hx30, hst, hld⟩ := frameOK_spec hf
  obtain ⟨n, hn⟩ : ∃ n, (body - fo) / 4 = n + 1 := ⟨(body - fo) / 4 - 1, by omega⟩
  rw [hn] at hw
  have h1 : (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az)))).eval ⟨sA, sym⟩ =
      sA.sp - BitVec.ofNat 64 az.toNat := by
    rw [Ex.eval_mkAdd]
    exact fr_neg _ haz
  have h2 : (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az - 8)))).eval ⟨sA, sym⟩ =
      sA.sp - BitVec.ofNat 64 az.toNat - 8 := by
    rw [Ex.eval_mkAdd]
    exact fr_neg8 _ haz
  have hnil : NoNil ⟨sA, sym⟩ σ := by
    refine ⟨fun a m h => by simp [hld] at h, fun a m v h => ?_⟩
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    have hspn : az.toNat + 8 + 4096 ≤ sA.sp.toNat := by omega
    have ha : a = Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az))) ∨
        a = Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az - 8))) := by
      rcases hst with e | e <;> rw [e] at h <;>
        simp only [frameStores, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.cons_append, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h <;>
        rcases h with h | h <;> simp [h.1]
    simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
    rcases ha with rfl | rfl
    · rw [h1]
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h64] at hspn ⊢
      omega
    · rw [h2]
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h64,
        show (8 : BitVec 64).toNat = 8 from rfl] at hspn ⊢
      omega
  obtain ⟨s1, hrun, hcore, hx, hctl⟩ := symWords_sound (H := H) hlink hsz hret n fo {} σ _
    ⟨sA, sym⟩ sA hw rfl (fr_holds_init _) hpc hnil
  have hs1 : s1.sp = sA.sp - BitVec.ofNat 64 az.toNat := by rw [hcore.sp, hsp', h1]
  have h30 : s1.x 30 = sA.x 30 := by
    rw [hx (fun _ _ h => by cases h), hx30]
    rfl
  obtain ⟨hw1, hw2, hout⟩ := fr_frame_mem (s1 := s1) hst h1 h2 hcore.mem
  refine ⟨s1, hrun, ?_, hs1, by rw [hs1]; exact hw1, by rw [hs1]; exact hw2, ?_,
    fun k h20 h27 h29 => ?_, hcore.v, fun a ha => hout a (by rwa [hs1] at ha)⟩
  · simp only [CtlPc] at hctl
    rw [hctl]
    exact fr_at (by omega)
  · have e := hcore.x 29 (by omega)
    rw [h29, h2] at e
    rw [hs1]
    exact e
  · refine fr_reg hcore h27 (Or.inr h30) fun hk hm => hregs _ hm ?_ ?_
    · bv_omega
    · bv_omega

end Run

/-! ## `checkObj`'s frame size -/

@[simp] private theorem fr_throw {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl

@[simp] private theorem fr_ite_ok {ε α : Type} {c : Prop} [Decidable c] {e : ε}
    {b : Except ε α} {v : α} : ((if c then Except.error e else b) = .ok v) ↔ ¬c ∧ b = .ok v := by
  split <;> simp [*]

@[simp] private theorem fr_ite_ok' {ε α : Type} {c : Prop} [Decidable c] {e : ε}
    {b : Except ε α} {v : α} : ((if c then b else Except.error e) = .ok v) ↔ c ∧ b = .ok v := by
  split <;> simp [*]

/-- `checkObj`'s frame size is the `TEXT` offset modulo `2^32`: non-negative. -/
private theorem fr_az_nonneg {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    (h : checkObj ps spills o = .ok tab) : 0 ≤ tab.autosize := by
  unfold checkObj at h
  cases h0 : ps[0]? with
  | none =>
    rw [h0] at h
    cases h
  | some text =>
    rw [h0] at h
    simp only [bind, Except.bind, pure, Except.pure, fr_throw, fr_ite_ok, fr_ite_ok'] at h
    obtain ⟨-, -, -, -, h⟩ := h
    split at h
    case h_2 => cases h
    split at h
    · cases h
    split at h
    · cases h
    rw [fr_ite_ok] at h
    obtain ⟨-, h⟩ := h
    split at h
    · cases h
    split at h
    · split at h
      · cases h
      · cases h
        exact Int.emod_nonneg _ (by decide)
    · cases h
      exact Int.emod_nonneg _ (by decide)

/-! ## The prologue -/

theorem obj_entry {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    {base : BitVec 64} {sym : Nat → BitVec 64} {code : Code} {H : Hooks} {retM : BitVec 64}
    {room : Nat} {s0 : MState}
    (hc : checkObj ps spills o = .ok tab) (hlink : linkCode base sym o.text o.relocs.toList = .ok code)
    (hsz : o.text.size ≤ 2 ^ 64) (hret : code retM = none)
    (hE : MachEntry code base room s0) (hroom : tab.autosize + 8 ≤ room)
    (hg : (s0.x 28).toNat + 32 ≤ 2 ^ 64)
    (hpass : ∀ ce tail gOff, tab.check = some (ce, tail, gOff) → CheckPasses tab.autosize gOff s0) :
    ∃ s1, MStar H code retM s0 s1 ∧
      (if tab.autosize = 0 then s1 = s0 else BodyEntry tab.autosize.toNat s0 s1) ∧
      s1.pc = base + BitVec.ofNat 64 (tab.offs[0]!) ∧
      (∀ k : Reg, k ≠ 16 → k ≠ 17 → k ≠ 20 → k ≠ 27 → k ≠ 29 → s1.x k = s0.x k) ∧
      s1.v = s0.v ∧ (∀ a, 16 ≤ (a - (s1.sp - 8)).toNat → s1.mem a = s0.mem a) := by
  obtain ⟨-, body, -, -, -, -, -, -, h0, -, -, hpro, -, -⟩ := checkObj_spec hc
  have haz0 := fr_az_nonneg hc
  have hoff : tab.offs[0]! = body := by simp [getElem!_def, h0]
  rw [hoff]
  rcases checkPrologue_spec hpro with ⟨haz, rfl, -⟩ | ⟨haz, fo, σ, hchk, hfo, hmod, hw, hf⟩
  · refine ⟨s0, .refl, by simp [haz], by simp [hE.pc], fun _ _ _ _ _ _ => rfl, rfl,
      fun _ _ => rfl⟩
  -- the state at the frame words
  obtain ⟨sA, hrunA, hpcA, hspA, hxA, hvA, hmA⟩ :
      ∃ sA, MStar H code retM s0 sA ∧ sA.pc = base + BitVec.ofNat 64 fo ∧ sA.sp = s0.sp ∧
        (∀ k : Reg, k ≠ 16 → k ≠ 17 → k ≠ 27 → sA.x k = s0.x k) ∧ sA.v = s0.v ∧
        sA.mem = s0.mem := by
    rcases hchk with ⟨-, rfl⟩ | ⟨ce, tail, gOff, hck, rfl, hgo, hcs⟩
    · exact ⟨s0, .refl, by simp [hE.pc], rfl, fun _ _ _ _ => rfl, rfl, rfl⟩
    · exact check_run hlink hsz hret hcs hE.pc hE.gOutside hg (by omega) (hpass _ _ _ hck)
  have hsp : 4096 + tab.autosize + 8 ≤ (sA.sp.toNat : Int) := by
    have := hE.room
    rw [hspA]
    omega
  obtain ⟨s1, hrun1, hpc1, hsp1, hlr, hfp, h29, hx1, hv1, hm1⟩ :=
    frame_run hlink hsz hret hw hf hfo hmod hpcA haz0 hsp
  refine ⟨s1, mstar_trans hrunA hrun1, ?_, hpc1, fun k h16 h17 h20 h27 h29 => ?_, ?_,
    fun a ha => ?_⟩
  · simp only [haz, ↓reduceIte]
    exact { sp := by rw [hsp1, hspA]
            lr := by rw [hlr, hxA 30 (by decide) (by decide) (by decide)]
            fp := by rw [hfp, hxA 29 (by decide) (by decide) (by decide)]
            r29 := h29
            g := by rw [hx1 28 (by decide) (by decide) (by decide),
              hxA 28 (by decide) (by decide) (by decide)] }
  · rw [hx1 k h20 h27 h29, hxA k h16 h17 h27]
  · rw [hv1, hvA]
  · rw [hm1 a ha, hmA]

/-! ## The epilogue -/

theorem obj_exit {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    {base : BitVec 64} {sym : Nat → BitVec 64} {code : Code} {H : Hooks} {retM : BitVec 64}
    {k : Nat} {t : MState}
    (hc : checkObj ps spills o = .ok tab) (hlink : linkCode base sym o.text o.relocs.toList = .ok code)
    (hsz : o.text.size ≤ 2 ^ 64) (hret : code retM = none) (hk : k < ps.size)
    (hr : ps[k].as = .RET) (hto : ps[k].to.type = .NONE) (hnosym : ps[k].to.sym = none)
    (hpc : t.pc = base + BitVec.ofNat 64 (tab.offs[k]!))
    (hsp : 4096 + 8 ≤ t.sp.toNat ∧ t.sp.toNat + 8 ≤ 2 ^ 64) :
    ∃ t', MStar H code retM t t' ∧
      t'.pc = (if tab.autosize = 0 ∨ tab.leaf then t.x 30 else t.word t.sp) ∧
      t'.x 30 = (if tab.autosize = 0 ∨ tab.leaf then t.x 30 else t.word t.sp) ∧
      t'.sp = t.sp + BitVec.ofInt 64 tab.autosize ∧
      t'.x 29 = (if tab.autosize = 0 then t.x 29
        else if tab.leaf then t.sp + BitVec.ofInt 64 (tab.autosize - 8) else t.word (t.sp - 8)) ∧
      (∀ r : Reg, r ≠ 27 → r ≠ 29 → r ≠ 30 → t'.x r = t.x r) ∧ t'.v = t.v ∧ t'.mem = t.mem ∧
      t'.nzcv = t.nzcv := by
  obtain ⟨text, -, hps0, hT, -, -, -, hlen, -, -, -, -, -, hbody⟩ := checkObj_spec hc
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Array.getElem?_eq_getElem hk, Option.some.injEq] at hps0
    rw [hps0, hT] at hr
    cases hr
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hone := checkBody_spec _ _ _ hbody (by simp [hlen]) j (by simp; omega)
  have hp : (ps.toList.drop 1)[j]'(by simp; omega) = ps[j + 1] := by simp
  have hs : (tab.offs.toList.drop 1)[j]'(by simp [hlen]; omega) = tab.offs[j + 1]! := by
    simp [hlen, hk]
  rw [hp, hs] at hone
  generalize ((tab.offs.toList.drop 1).getD (j + 1) tab.endOff) = e at hone
  obtain ⟨-, hlt, hmod, σ, c, hw, hok⟩ := (checkOne_spec hone).resolve_right fun ⟨hne, _⟩ => by
    simp [isRet0, hr, hto] at hne
  have hback : retBack tab.autosize tab.leaf ps[j + 1] =
      .reg (if tab.autosize == 0 || tab.leaf then .x 30 else .ld 8 .sp) := by
    simp [retBack, hnosym]
  rw [hback] at hok
  obtain ⟨n, hn⟩ : ∃ n, (e - tab.offs[j + 1]!) / 4 = n + 1 :=
    ⟨(e - tab.offs[j + 1]!) / 4 - 1, by omega⟩
  rw [hn] at hw
  rcases retOK_spec hok with ⟨haz, rfl, rfl⟩ |
      ⟨haz, hsp', h29, h30', hregs, hfl, hst, rfl, hld⟩
  · -- frameless: the words only return
    obtain ⟨t', hrun, hcore, hx, hctl⟩ := symWords_sound (H := H) hlink hsz hret n _ {} {} _
      ⟨t, sym⟩ t hw rfl (fr_holds_init _) hpc ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
    have h30 : t'.x 30 = t.x 30 := by
      rw [hx (fun _ _ h => by cases h)]
      rfl
    simp only [CtlPc, haz, beq_self_eq_true, Bool.true_or, ↓reduceIte] at hctl
    refine ⟨t', hrun, ?_, ?_, ?_, ?_, fun r h27 _ _ => fr_reg hcore h27 (Or.inr h30)
      fun _ _ => rfl, hcore.v, hcore.mem, hcore.nzcv⟩
    · simp only [haz, true_or, ↓reduceIte, hctl]
      rfl
    · simp only [haz, true_or, ↓reduceIte, h30]
    · rw [hcore.sp, haz]
      simp
      rfl
    · simp only [haz, ↓reduceIte]
      exact hcore.x 29 (by omega)
  · -- framed: pop the frame, restore `R29` (and `R30`), return
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    have hnil : NoNil ⟨t, sym⟩ σ := by
      refine ⟨fun a m h => ?_, fun a m v h => by simp [hst] at h⟩
      simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
      rcases hld (a, m) h with e | e <;> simp only [Prod.mk.injEq] at e <;> rw [e.1]
      · rw [Ex.eval_mkAdd]
        show 4096 ≤ (t.sp + BitVec.ofInt 64 (-8)).toNat
        rw [fr_m8]
        simp only [BitVec.toNat_sub, h64, show (8 : BitVec 64).toNat = 8 from rfl]
        omega
      · show 4096 ≤ t.sp.toNat
        omega
    obtain ⟨t', hrun, hcore, hx, hctl⟩ := symWords_sound (H := H) hlink hsz hret n _ {} σ _
      ⟨t, sym⟩ t hw rfl (fr_holds_init _) hpc hnil
    have h30 := hx (fun _ _ h => by cases h)
    have h29' : t'.x 29 = (σ.getX 29).eval ⟨t, sym⟩ := hcore.x 29 (by omega)
    simp only [CtlPc] at hctl
    rw [h30'] at h30
    rw [h29] at h29'
    refine ⟨t', hrun, ?_, ?_, ?_, ?_, fun r h27 h29r h30r => fr_reg hcore h27 (Or.inl h30r)
      fun hk hm => hregs _ hm (by bv_omega), hcore.v, by rw [hcore.mem, hst]; rfl,
      by rw [hcore.nzcv, hfl]; rfl⟩
    · rw [hctl]
      cases tab.leaf <;> simp [haz, Ex.eval, fr_wordR]
    · rw [h30]
      cases tab.leaf <;> simp [haz, Ex.eval, fr_wordR]
    · rw [hcore.sp, hsp', Ex.eval_mkAdd]
      rfl
    · rw [h29']
      cases tab.leaf
      · simp [haz, Ex.eval, Ex.eval_mkAdd, fr_wordR]
        rw [show t.sp + 18446744073709551608#64 = t.sp - 8#64 by bv_omega]
      · simp [haz, Ex.eval, Ex.eval_mkAdd]

end GoFV.Proof.Obj
