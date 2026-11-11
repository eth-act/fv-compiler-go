import GoFV.Proof.Gen.Step61
import GoFV.Proof.Gen.Progs61
import GoFV.Proof.Gen.G54a
import GoFV.Proof.Gen.G32

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G61's group A: values and the state after a value (`docs/plans/proofs3.md` §4)

The values `runLoc` and the machine compute for an atomic of group A, related: the location's old
integer (`old_rel61`) and, at the result's shape, the old value (`res_rel61`), both against the
zero extension of the `n` bytes the machine loads; `Int` ops of two related integers against the
machine's 64-bit op (`valRel_int2`); the zero flag of a compare (`subFlags_z64`, `subFlags_z32`);
the low bytes an LSE instruction stores (`maskN_store`).

`atom_finish`: after the machine ran the value's Progs, changing (in the X registers) at most the
result's register, `R27` and the temporary, the memory as the store's `MemInj` says and outside
the frame, and the flags only for a compare-and-swap, `LocMatch` and the invariants hold of
`runLoc`'s state: its clobbers, the result in its register and the new memory.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

variable {ι : Blk → Option (BitVec 64)}

/-! ## Values -/

theorem widthN_bits {n : Nat} (hn : n = 8 ∨ n = 4 ∨ n = 1) : (widthN n).bits = 8 * n := by
  rcases hn with rfl | rfl | rfl <;> rfl

/-- An integer and a register related: the register's low bits are the integer. -/
theorem valRel_int_iff (hA : AddrAgree ι) {w : Width} {a : BitVec w.bits} {r : BitVec 64} :
    ValRel ι (.int w a) r ↔ r.setWidth w.bits = a := by
  cases w with
  | w64 =>
    constructor
    · intro h; rw [valRel_i64 hA h]; exact BitVec.setWidth_eq a
    · intro h; exact .inl (by rw [← h]; exact (BitVec.setWidth_eq r).symm)
  | w8 => exact Iff.rfl
  | w16 => exact Iff.rfl
  | w32 => exact Iff.rfl

/-- A binary integer op of `Int` (`int2`) of two values whose integers are the low bits of `A`
and `B`, against a machine op `C` whose low bits are the op's of theirs. -/
theorem valRel_int2 (hA : AddrAgree ι) {w : Width}
    {g : BitVec w.bits → BitVec w.bits → BitVec w.bits} {x y : Val} {A B C : BitVec 64}
    (hx : ∀ a, x.asInt w = some a → A.setWidth w.bits = a)
    (hy : ∀ b, y.asInt w = some b → B.setWidth w.bits = b)
    (hC : C.setWidth w.bits = g (A.setWidth w.bits) (B.setWidth w.bits)) :
    ValRel ι (int2 w (fun a b => .int w (g a b)) [x, y]) C := by
  simp only [int2]
  cases hxa : x.asInt w with
  | none => trivial
  | some a =>
    cases hyb : y.asInt w with
    | none => trivial
    | some b =>
      simp only
      rw [valRel_int_iff hA, hC, hx a hxa, hy b hyb]

theorem fits_int2 {w : Width} {g : BitVec w.bits → BitVec w.bits → BitVec w.bits} {x y : Val} :
    Fits w.bits (int2 w (fun a b => .int w (g a b)) [x, y]) := by
  simp only [int2]
  split <;> trivial

/-- An operand of class `8n` fitted to the location's shape: if it reads as an integer of the
location's width, that is the register's low bits. -/
theorem fit_asInt61 (hA : AddrAgree ι) {w : Width} {y : Val} {R : BitVec 64}
    (hy : ValRel ι y R) (hf : Fits w.bits y) :
    ∀ b, (fitPiece (.int w) y).asInt w = some b → R.setWidth w.bits = b := by
  intro b hb
  cases y with
  | int w' x =>
    have hw : w'.bits = w.bits := hf
    have hww : w' = w := by cases w <;> cases w' <;> first | rfl | exact absurd hw (by decide)
    subst hww
    simp only [fitPiece, beq_self_eq_true, ↓reduceIte, Val.asInt_int, Option.some.injEq] at hb
    subst hb
    exact (valRel_int_iff hA).1 hy
  | ptr q =>
    have hw : w.bits = 64 := hf
    have : w = .w64 := by cases w <;> first | rfl | exact absurd hw (by decide)
    subst this
    simp [fitPiece, Val.asInt] at hb
  | poison => cases w <;> simp [fitPiece, Val.asInt] at hb
  | bool bb => have hw : w.bits = 1 := hf; cases w <;> exact absurd hw (by decide)
  | _ => exact False.elim hf

/-- A write that succeeds covers bytes a read of the same size gets. -/
theorem read_of_canWrite {m : Mem} {p : Ptr} {n : Nat} (h : m.canWrite p n = true) (hn : 0 < n) :
    ∃ bs, m.read p n = some bs := by
  unfold Mem.canWrite at h
  have hn' : (n == 0) = false := by simp; omega
  simp only [hn', Bool.false_or] at h
  unfold Mem.read
  cases hf : m.find? p.blk with
  | none => rw [hf] at h; cases h
  | some a =>
    rw [hf] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [hn', Bool.false_eq_true, ↓reduceIte, hf, Option.bind_eq_bind, Option.bind_some]
    exact ⟨_, if_pos ⟨h.1.1.2, h.1.2, h.2⟩⟩

/-- The integer at an aligned `n`-byte location of a valid block is the low bits of the zero
extension of the `n` bytes at its injected address. -/
theorem old_rel61 (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm) {p : Ptr}
    {a : BitVec 64} {n : Nat} (hn : n = 8 ∨ n = 4 ∨ n = 1) (ha : ι p.blk = some a)
    (hal : Atomic.aligned p n = true) (hr : ∃ bs, m.read p n = some bs) :
    ∀ c, (m.load (.int (widthN n)) p).asInt (widthN n) = some c →
      ((readMem mm (a + p.off) n).setWidth 64).setWidth (widthN n).bits = c := by
  intro c hc
  obtain ⟨bs, hbs⟩ := hr
  have hcl : Gen.Check.cls (.int (widthN n)) = some (8 * n) := by
    simp only [Gen.Check.cls, widthN_bits hn]
  have hv := valRel_ldar hA h (by omega) hcl ha hbs
  have hsz : (Ty.int (widthN n)).size = n := by rcases hn with rfl | rfl | rfl <;> rfl
  simp only [Atomic.aligned, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hal
  rw [hsz] at hv
  have hc0 : (n == 0 || p.off.toNat % n != 0) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, bne_eq_false_iff_eq]
    exact ⟨hal.1, hal.2⟩
  rw [hc0] at hv
  simp only [Bool.false_eq_true, ↓reduceIte] at hv
  cases hl : m.load (.int (widthN n)) p with
  | int w' x =>
    rw [hl] at hc hv
    simp only [Val.asInt] at hc
    split at hc
    · rename_i he
      subst he
      simp only [Option.some.injEq] at hc
      subst hc
      rw [retypeL_int_self] at hv
      exact (valRel_int_iff hA).1 hv
    · cases hc
  | _ => rw [hl] at hc; simp [Val.asInt] at hc

/-- The location's value at the result's shape `t0` (class `8n`) is related to the zero
extension of its `n` bytes. -/
theorem res_rel61 (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm) {p : Ptr}
    {a : BitVec 64} {n : Nat} {t0 : Ty} (hn : n = 8 ∨ n = 4 ∨ n = 1)
    (hc0 : Gen.Check.cls t0 = some (8 * n)) (ha : ι p.blk = some a)
    (hal : Atomic.aligned p n = true) (hr : ∃ bs, m.read p n = some bs) :
    ValRel ι ((m.load (.int (widthN n)) p).retypeL t0) ((readMem mm (a + p.off) n).setWidth 64) := by
  obtain ⟨bs, hbs⟩ := hr
  have hv := valRel_ldar hA h (by omega) hc0 ha hbs
  have hsz : t0.size = n := by
    cases t0 with
    | int w => simp only [Gen.Check.cls, Option.some.injEq] at hc0; cases w <;>
        simp [Ty.size, Width.bytes, Width.bits] at hc0 ⊢ <;> omega
    | ptr _ => simp only [Gen.Check.cls, Option.some.injEq] at hc0; simp [Ty.size]; omega
    | bool => simp [Gen.Check.cls] at hc0; omega
    | _ => simp [Gen.Check.cls] at hc0
  simp only [Atomic.aligned, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hal
  have hc1 : (t0.size == 0 || p.off.toNat % t0.size != 0) = false := by
    rw [hsz]
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, bne_eq_false_iff_eq]
    exact ⟨hal.1, hal.2⟩
  rw [hc1] at hv
  simp only [Bool.false_eq_true, ↓reduceIte] at hv
  have heq : (m.load (.int (widthN n)) p).retypeL t0 = (m.load t0 p).retypeL t0 := by
    cases t0 with
    | int w =>
      simp only [Gen.Check.cls, Option.some.injEq] at hc0
      have : w = widthN n := by
        rcases hn with rfl | rfl | rfl <;> cases w <;> first | rfl | (simp [Width.bits] at hc0)
      rw [this]
    | ptr e =>
      simp only [Gen.Check.cls, Option.some.injEq] at hc0
      obtain rfl : n = 8 := by omega
      have hl : m.load (.ptr e) p = m.load (.int .w64) p := by
        simp only [Mem.load, Ty.size, Width.bytes, Width.bits, Nat.reduceDiv]
        cases m.read p 8 with
        | none => rfl
        | some bs => simp only [decodeLoad, Sem.decode, decodePtr_eq]; rfl
      rw [hl]; rfl
    | bool => simp [Gen.Check.cls] at hc0; omega
    | _ => simp [Gen.Check.cls] at hc0
  rw [heq]
  exact hv

/-- The low `8n` bits of `maskN n` are those of the value. -/
theorem maskN_store {n : Nat} (hn : n = 8 ∨ n = 4 ∨ n = 1) (V : BitVec 64) :
    BitVec.ofNat (8 * n) (ProgOp.maskN n V).toNat = BitVec.ofNat (8 * n) (V.toNat % 2 ^ (8 * n)) := by
  have hV := V.isLt
  rcases hn with rfl | rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    simp only [ProgOp.maskN, beq_self_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
    omega
  · apply BitVec.eq_of_toNat_eq
    have hm : (4 == 8) = false := rfl
    simp only [ProgOp.maskN, hm, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat,
      BitVec.toNat_and]
    rw [show (2 ^ (8 * 4) - 1) % 2 ^ 64 = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  · apply BitVec.eq_of_toNat_eq
    have hm : (1 == 8) = false := rfl
    simp only [ProgOp.maskN, hm, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat,
      BitVec.toNat_and]
    rw [show (2 ^ (8 * 1) - 1) % 2 ^ 64 = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The zero flag of a 64-bit compare: the operands are equal. -/
theorem subFlags_z64 (x y : BitVec 64) : (Arm64.subFlags x y).2.z = (x == y) := by
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  simp only [Arm64.subFlags, addWithCarry, ↓reduceIte]
  have hx := x.isLt
  have hy := y.isLt
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, BitVec.toNat_not, h0] at this
    apply BitVec.eq_of_toNat_eq
    omega
  · rintro rfl
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_not, h0]
    omega

/-- The zero flag of a 32-bit compare: the operands are equal. -/
theorem subFlags_z32 (x y : BitVec 32) : (Arm64.subFlags x y).2.z = (x == y) := by
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  simp only [Arm64.subFlags, addWithCarry, ↓reduceIte]
  have hx := x.isLt
  have hy := y.isLt
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, BitVec.toNat_not, h0] at this
    apply BitVec.eq_of_toNat_eq
    omega
  · rintro rfl
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_not, h0]
    omega

/-! ## The state after a value -/

section Finish

variable {E : MatchEnv} {lc : LocCtx} {s : LocState} {b : ID} {i : Nat} {m m' : MState}
  {v : Value} {K : Nat → Option Nat}

/-- `LocState.clobber` keeps the slots and the memory. -/
theorem clobber_sm61 (s : LocState) :
    (s.clobber lc v).slots = s.slots ∧ (s.clobber lc v).mem = s.mem := by
  rw [clobber_eq54]
  have hA : ∀ (b : Bool) (i : Nat) (s : LocState), (clobArg54 lc v b i s).slots = s.slots ∧
      (clobArg54 lc v b i s).mem = s.mem := by
    intro b i s
    unfold clobArg54
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩
  have hT : ∀ s : LocState, (clobTemp54 lc v s).slots = s.slots ∧
      (clobTemp54 lc v s).mem = s.mem := by
    intro s; unfold clobTemp54; split <;> exact ⟨rfl, rfl⟩
  have hM : ∀ msk : RegMask, (s.clobberMask msk).slots = s.slots ∧
      (s.clobberMask msk).mem = s.mem := by
    intro msk; unfold LocState.clobberMask; split <;> exact ⟨rfl, rfl⟩
  obtain ⟨h1, h3⟩ := hM v.op.regInfo.clobbers
  obtain ⟨h4, h6⟩ := hA v.op.regInfo.clobbersArg1 1 (s.clobberMask v.op.regInfo.clobbers)
  obtain ⟨h7, h9⟩ := hA v.op.regInfo.clobbersArg0 0
    (clobArg54 lc v v.op.regInfo.clobbersArg1 1 (s.clobberMask v.op.regInfo.clobbers))
  obtain ⟨h10, h12⟩ := hT (clobArg54 lc v v.op.regInfo.clobbersArg0 0
    (clobArg54 lc v v.op.regInfo.clobbersArg1 1 (s.clobberMask v.op.regInfo.clobbers)))
  split
  · exact ⟨h10.trans (h7.trans (h4.trans h1)), h12.trans (h9.trans (h6.trans h3))⟩
  · exact ⟨h10.trans (h7.trans (h4.trans h1)), h12.trans (h9.trans (h6.trans h3))⟩

/-- The flags after `LocState.clobber`: `poison` for an op that clobbers them, else unchanged. -/
theorem clobber_flags61 (s : LocState) :
    (s.clobber lc v).flags = if v.op.clobberFlags then .poison else s.flags := by
  split
  · rename_i hf
    rw [clobber_eq54, if_pos hf]
  · rename_i hf
    exact (clobber_keeps54 s (by simpa using hf)).2.1

theorem objX?_zero {k : Reg} : objX? zeroReg ≠ some k := fun h => by
  have := (objX?_some h).1
  unfold zeroReg at this
  omega

/-- After a value of group A: the machine `m'` changed at most `Rd` (`X kd`, holding the result
`y`), `R27` and the temporary among the X registers (none of `R28`–`R30`), the memory as `MemInj`
of the new memory says and not in the frame, the flags only if the op clobbers them, and is at
the next value's PC: `runLoc`'s clobbers, `y` in `r` and the new memory are related to it, with
the invariants. -/
theorem atom_finish (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    {r kd : Nat} (hkd : kd < 32) (hrk : objOf? r = some (REG_R0 + kd)) (hd : destOK r = true)
    (hrz : r ≠ zeroReg) {y : Val} {c : Nat} (hfy : Fits c y)
    (hy : ValRel E.ι y (m'.x (BitVec.ofNat 5 kd)))
    {mm' : Mem} (hM : MemInj E.ι mm' m'.mem) (hkn : KeysNodup mm')
    (hsep : SepAt osp E.ι (StkAt E) mm') (hP : ∀ a, StkAt E a → m'.mem a = m.mem a)
    (htd : ∀ t, (lc.temps[v.id]?).join = some t → t < 26)
    (hx : ∀ q : Reg, q ≠ BitVec.ofNat 5 kd → q ≠ BitVec.ofNat 5 27 →
      (∀ t, (lc.temps[v.id]?).join = some t → objX? t ≠ some q) → m'.x q = m.x q)
    (hv : m'.v = m.v) (hsp : m'.sp = m.sp) (hfl : v.op.clobberFlags = false → m'.nzcv = m.nzcv)
    (hpc : m'.pc = E.pcOf b (i + 1)) :
    LocMatch E { (s.clobber lc v).setReg r y with mem := .mem mm' } b (i + 1) m' ∧
      CoreInv E.ι (StkAt E) (kSet K r (some c)) { (s.clobber lc v).setReg r y with mem := .mem mm' }
        osp ∧
      SlotInv lc { (s.clobber lc v).setReg r y with mem := .mem mm' } := by
  rcases objOf?_dest hkd hrk hd with ⟨h, -⟩ | ⟨hr26, hk27, hobj⟩
  · exact absurd h hrz
  obtain ⟨hcsl, hcmem⟩ := clobber_sm61 (lc := lc) (v := v) s
  have hk31 : (BitVec.ofNat 5 kd : Reg) ≠ 31 := by
    intro he; have := congrArg BitVec.toNat he; simp at this; omega
  let m0 : MState :=
    { m' with x := fun q => if q = BitVec.ofNat 5 kd then m.x q else m'.x q }
  -- the high registers and the ones `runLoc` keeps
  have hhi : ∀ q : Nat, 28 ≤ q → q < 31 → m0.x (BitVec.ofNat 5 q) = m.x (BitVec.ofNat 5 q) := by
    intro q h1 h2
    show (if _ then _ else _) = _
    split
    · rfl
    refine hx _ ?_ ?_ ?_
    · intro he; have := congrArg BitVec.toNat he; simp at this; omega
    · intro he; have := congrArg BitVec.toNat he; simp at this; omega
    · intro t ht he
      have h1' := objX?_lt27 he (htd t ht)
      simp at h1'; omega
  have hm0x : ∀ r' x, (s.clobber lc v).regs[r']? = some x → x = .poison ∨
      (s.regs[r']? = some x ∧ ∀ q, objX? r' = some q → m0.x q = m.x q) := by
    intro r' x h
    rcases clobber_get54 h with rfl | ⟨h2, -, -, -, htp⟩
    · exact .inl rfl
    refine .inr ⟨h2, fun q hq => ?_⟩
    show (if q = BitVec.ofNat 5 kd then m.x q else m'.x q) = m.x q
    split
    · rfl
    · rename_i hne
      refine hx q hne (objX?_ne27 hq) fun t ht he => ?_
      have := objX?_inj he hq
      subst this
      exact objX?_zero (htp ht ▸ he)
  obtain ⟨hslots, hframe⟩ := stk_slots_frame (E' := E) (m' := m0) hm hF hsz rfl
    (fun _ _ h => h) hP hsp (hhi 28 (by omega) (by omega)) (hhi 29 (by omega) (by omega))
    (fun _ => hhi 30 (by omega) (by omega))
  have hm1 : LocMatch E { s.clobber lc v with mem := .mem mm' } b (i + 1) m0 := by
    refine ⟨fun r' x h => ?_, ?_, ?_, ⟨mm', rfl, hM⟩, hframe, hpc⟩
    · rcases hm0x r' x h with rfl | ⟨h2, hx0⟩
      · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
      · obtain ⟨hx1, hv1⟩ := hm.regs r' x h2
        refine ⟨fun q hq => ?_, fun q hq => ?_⟩
        · rw [hx0 q hq]; exact hx1 q hq
        · show VRel E.ι x (m'.v q); rw [hv]; exact hv1 q hq
    · show FlagsRel (s.clobber lc v).flags m'.nzcv
      rw [clobber_flags61]
      split
      · trivial
      · rename_i hf
        rw [hfl (by simpa using hf)]
        exact hm.flags
    · show ∀ k y, (s.clobber lc v).slots.lookup k = some y → _
      rw [hcsl]
      exact hslots
  have hset := locMatch_setReg hm1 hkd hrk hd (x := y) (val := m'.x (BitVec.ofNat 5 kd))
    (hy) (b' := b) (i' := i + 1)
  have hmeq : ({ m0.wX (BitVec.ofNat 5 kd) (m'.x (BitVec.ofNat 5 kd)) with
      pc := E.pcOf b (i + 1) } : MState) = m' := by
    rw [← hpc]
    simp only [MState.wX, hk31, ↓reduceIte, m0]
    cases m'
    simp only [MState.mk.injEq, and_true]
    funext q
    split <;> simp_all
  rw [hmeq] at hset
  refine ⟨hset, ?_, fun k y hk => hsi k y ?_⟩
  · have hc1 : CoreInv E.ι (StkAt E) K { s.clobber lc v with mem := .mem mm' } osp :=
      ⟨fun r' x c' hrz' h hc => by
        rcases clobber_get54 h with rfl | ⟨h2, -⟩
        · trivial
        · exact hinv.regs r' x c' hrz' h2 hc, mm', rfl, hkn, hsep⟩
    exact core_setReg hc1 hfy
  · show s.slots.lookup k = some y
    rw [← hcsl]; exact hk

end Finish

end GoFV.Proof.Gen
