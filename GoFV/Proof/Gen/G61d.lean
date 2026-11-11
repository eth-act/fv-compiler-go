import GoFV.Proof.Gen.G61a

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G61, group A: the LSE atomics (`docs/plans/proofs3.md` §4)

The `*Variant` values of `vkind61a` (`GoFV/Gen/Check61a.lean`), from `runLoc`'s step (`Step61.lean`)
to the machine's run of their Progs (`Progs61.lean`), related by `atom_finish` (`G61V.lean`). No
loop: each value is one LSE instruction with straight-line Progs around it.

* The read-modify-writes (`g61_lse`): `SWPAL`, `LDADDAL` then `ADD Rv, Rd`, `MVN Rv, R27` then
  `LDCLRAL R27`, `LDORAL` (`lse_run61d`). The LSE instruction loads the location's `n` bytes into
  `Rd` and stores the low `n` bytes of `lseF` of them and its operand (`progStep_lse`,
  `maskN_store`); `MVN` makes `LDCLRAL`'s cleared bits the complement of `Rv`'s, so the stored
  word is `lseG61d f old Rv` and `Rd` ends as `lseR61d f old Rv` (the sum for `addV`, else the old
  word). `runLoc` stores `Atomic.step (kindF f)` of the location's integer and the fitted operand
  (`lse_store61d`) and returns it or the old value (`lse_res61d`), related by `valRel_int2`,
  `old_rel61`, `fit_asInt61` and `res_rel61`.
* The compare-and-swap (`g61_casV`): `MOVD`/`MOVW Ro, R27`, `CASAL R27, (Rp), Rn`,
  `CMP`/`CMPW Ro, R27`, `CSET EQ, Rd` (`casV_run61d`). `CASAL` compares the location's
  zero-extended bytes with `maskN n R27`, which is `maskN n Ro` (`MOVW`'s sign extension keeps
  the low word, `maskN_sext61d`); the compare sees the same equality (`beq_maskN61d`), so `Rd` is 1
  exactly when the store happened. `runLoc`'s `Atomic.cas` compares the location's integer with
  the fitted `old` (`stepLoc_cas61`): the same low bits; its boolean result is `CSET`'s 0/1.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## Words -/

/-- The word an LSE read-modify-write of family `f` stores, from the location's old word `o` and
the operand register `v` (`andV`: `LDCLRAL` of `MVN v` keeps the bits of `v`). -/
def lseG61d (f : AtomF61) (o v : BitVec 64) : BitVec 64 :=
  match f with
  | .xchgV => v
  | .addV => o + v
  | .andV => o &&& v
  | _ => o ||| v

/-- The word in `Rd` after an LSE read-modify-write of family `f` (`addV`: the sum, else the old
word). -/
def lseR61d (f : AtomF61) (o v : BitVec 64) : BitVec 64 :=
  match f with
  | .addV => o + v
  | _ => o

/-- `maskN 4` sees only the low word, which `MOVW`'s sign extension keeps. -/
theorem maskN_sext61d (X : BitVec 64) :
    ProgOp.maskN 4 (ProgOp.sextTo64 4 X) = ProgOp.maskN 4 X := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : (4 == 8) = false := rfl
  simp only [ProgOp.maskN, hm, Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_and,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases h : i < 32
  · rw [show ProgOp.sextTo64 4 X = Arm64.sext 32 X from rfl,
      sext_bit 32 ⟨by omega, by omega⟩ X i hi]
    simp only [h, ↓reduceIte]
  · simp [show ¬ i < 8 * 4 by omega]

omit [GoFV.SSA.Sem.Addrs] in
/-- A zero-extended location word equals `maskN n X` exactly when its low `8n` bits are `X`'s. -/
theorem beq_maskN61d {n : Nat} (hn : n = 8 ∨ n = 4) (R : BitVec (8 * n)) (X : BitVec 64) :
    (R.setWidth 64 == ProgOp.maskN n X) =
      ((R.setWidth 64).setWidth (widthN n).bits == X.setWidth (widthN n).bits) := by
  rcases hn with rfl | rfl
  · show (R.setWidth 64 == X) = ((R.setWidth 64).setWidth 64 == X.setWidth 64)
    simp only [BitVec.setWidth_eq]
  · have hm : (4 == 8) = false := rfl
    have hR := R.isLt
    have hX := X.isLt
    simp only [ProgOp.maskN, hm, Bool.false_eq_true, ↓reduceIte]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, BitVec.toNat_eq, BitVec.toNat_eq,
      BitVec.toNat_and]
    show _ ↔ (R.setWidth 64).toNat % 2 ^ 32 = X.toNat % 2 ^ 32
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (2 ^ (8 * 4) - 1) % 2 ^ 64 = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    have : R.toNat % 2 ^ 64 = R.toNat := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.mod_eq_of_lt (by omega : R.toNat < 2 ^ 32)]

/-! ## Values -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

/-- An integer op's result stays itself when fitted to its own width. -/
theorem fitPiece_int2_61d {w : Width} {g : BitVec w.bits → BitVec w.bits → BitVec w.bits}
    {x y : Val} : fitPiece (.int w) (int2 w (fun a b => .int w (g a b)) [x, y]) =
      int2 w (fun a b => .int w (g a b)) [x, y] := by
  simp only [int2]
  split <;> simp [fitPiece]

/-- A location that loads as an integer has its bytes. -/
theorem read_of_load61d {mm : Mem} {w : Width} {p : Ptr} {c : BitVec w.bits}
    (h : (mm.load (.int w) p).asInt w = some c) : ∃ bs, mm.read p w.bytes = some bs := by
  have hl : mm.load (.int w) p = (match mm.read p (Ty.int w).size with
      | some bs => decodeLoad bs 0 (.int w)
      | none => .poison) := rfl
  rw [hl] at h
  cases hr : mm.read p (Ty.int w).size with
  | none => rw [hr] at h; simp [Val.asInt] at h
  | some bs => exact ⟨bs, hr⟩

omit [GoFV.SSA.Sem.Addrs] in
theorem fits_eq61d {c c' : Nat} {v : Val} (h : c = c') (hv : Fits c v) : Fits c' v := h ▸ hv

/-- What an LSE read-modify-write stores: the fitted operand (`xchgV`) or `Int` of the old value
and the fitted operand, a value of the location's width related to `lseG61d f O Y`. -/
theorem lse_store61d (hA : AddrAgree ι) {f : AtomF61} {n : Nat}
    (hf : f = .xchgV ∨ f = .addV ∨ f = .andV ∨ f = .orV) (hn : n = 8 ∨ n = 4 ∨ n = 1)
    {old y : Val} {O Y : BitVec 64}
    (hO : ∀ c, old.asInt (widthN n) = some c → O.setWidth (widthN n).bits = c)
    (hy : ValRel ι y Y) (hyf : Fits (8 * n) y) :
    ∃ z, (Atomic.step (kindF f) (widthN n) old (fitPiece (.int (widthN n)) y)).1 =
        fitPiece (.int (widthN n)) z ∧ Fits (8 * n) z ∧ ValRel ι z (lseG61d f O Y) := by
  have hyf' : Fits (widthN n).bits y := by rw [widthN_bits hn]; exact hyf
  have hY := fit_asInt61 hA hy hyf'
  have hle : (widthN n).bits ≤ 64 := by rw [widthN_bits hn]; omega
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨y, rfl, hyf, hy⟩
  · refine ⟨GoFV.SSA.Sem.Int.add (widthN n) [old, fitPiece (.int (widthN n)) y],
      (fitPiece_int2_61d (g := fun a b => a + b)).symm, ?_, ?_⟩
    · exact fits_eq61d (widthN_bits hn) fits_int2
    · exact valRel_int2 (g := fun a b => a + b) hA hO hY (BitVec.setWidth_add O Y hle)
  · refine ⟨GoFV.SSA.Sem.Int.and (widthN n) [old, fitPiece (.int (widthN n)) y],
      (fitPiece_int2_61d (g := fun a b => a &&& b)).symm, ?_, ?_⟩
    · exact fits_eq61d (widthN_bits hn) fits_int2
    · exact valRel_int2 (g := fun a b => a &&& b) hA hO hY BitVec.setWidth_and
  · refine ⟨GoFV.SSA.Sem.Int.or (widthN n) [old, fitPiece (.int (widthN n)) y],
      (fitPiece_int2_61d (g := fun a b => a ||| b)).symm, ?_, ?_⟩
    · exact fits_eq61d (widthN_bits hn) fits_int2
    · exact valRel_int2 (g := fun a b => a ||| b) hA hO hY BitVec.setWidth_or

/-- What an LSE read-modify-write returns, at the result's shape `t0` (class `8n`): the old value,
or for `addV` the sum, related to `lseR61d f O Y`. -/
theorem lse_res61d (hA : AddrAgree ι) {f : AtomF61} {n : Nat}
    (hf : f = .xchgV ∨ f = .addV ∨ f = .andV ∨ f = .orV) (hn : n = 8 ∨ n = 4 ∨ n = 1)
    {t0 : Ty} (hc0 : cls t0 = some (8 * n)) {old y : Val} {O Y : BitVec 64}
    (hO : ∀ c, old.asInt (widthN n) = some c → O.setWidth (widthN n).bits = c)
    (hy : ValRel ι y Y) (hyf : Fits (8 * n) y) (hres : ValRel ι (old.retypeL t0) O) :
    ∃ rr, (Atomic.step (kindF f) (widthN n) old (fitPiece (.int (widthN n)) y)).2 = some rr ∧
      ValRel ι (rr.retypeL t0) (lseR61d f O Y) := by
  have hyf' : Fits (widthN n).bits y := by rw [widthN_bits hn]; exact hyf
  have hY := fit_asInt61 hA hy hyf'
  have hle : (widthN n).bits ≤ 64 := by rw [widthN_bits hn]; omega
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨old, rfl, hres⟩
  · refine ⟨GoFV.SSA.Sem.Int.add (widthN n) [old, fitPiece (.int (widthN n)) y], rfl, ?_⟩
    exact valRel_retypeL hA hc0 (fits_eq61d (widthN_bits hn) fits_int2)
      (valRel_int2 (g := fun a b => a + b) hA hO hY (BitVec.setWidth_add O Y hle))
  · exact ⟨old, rfl, hres⟩
  · exact ⟨old, rfl, hres⟩

end Vals

/-! ## Runs -/

section Runs

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64}

omit [GoFV.SSA.Sem.Addrs] in
theorem pstar_trans61d {L : Link} {ps : List Prog} {a b c : MState}
    (h1 : PStar H L ps ret a b) (h2 : PStar H L ps ret b c) : PStar H L ps ret a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact ih.tail hs

/-- One LSE read-modify-write `op Rs, (Rp), Rd` at `A`: the zero extension of the `n` bytes at `A`
in `X kd`, the low `n` bytes of `lseF f` of them and `X ks` stored. -/
theorem lse1_run61d (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {f : AtomF61} {n ks kp kd : Nat}
    (hf' : f = .xchgV ∧ (n = 8 ∨ n = 4 ∨ n = 1) ∨ f = .addV ∧ (n = 8 ∨ n = 4) ∨
      f = .andV ∧ (n = 8 ∨ n = 4 ∨ n = 1) ∨ f = .orV ∧ (n = 8 ∨ n = 4 ∨ n = 1))
    (hks : ks < 32) (hkp : kp < 31) (hkd : kd < 32) {j j' : Nat}
    (h : OneAt2 psA j (lsePat (lse61 f n) (REG_R0 + ks) (REG_R0 + kp) (REG_R0 + kd)) j')
    (m : MState) {A : BitVec 64} (hA : m.rX (BitVec.ofNat 5 kp) = A) (hnil : nilPage A = false) :
    PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
      { m with pc := pcAt text psA.toList j }
      { m.wX (BitVec.ofNat 5 kd) ((readMem m.mem A n).setWidth 64) with
        mem := writeMem m.mem A n (BitVec.ofNat (8 * n) (ProgOp.maskN n
          (lseF f ((readMem m.mem A n).setWidth 64) (m.rX (BitVec.ofNat 5 ks)))).toNat),
        pc := pcAt text psA.toList j' } := by
  obtain ⟨k, hk', hs⟩ := step1 (H := H) hnd hlt hret h m
    (f := fun k => { m.wX (BitVec.ofNat 5 kd) ((readMem m.mem A n).setWidth 64) with
        mem := writeMem m.mem A n (BitVec.ofNat (8 * n) (ProgOp.maskN n
          (lseF f ((readMem m.mem A n).setWidth 64) (m.rX (BitVec.ofNat 5 ks)))).toNat),
        pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      simp only [lsePat, Shape.okT, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, ht2⟩ := hok
      have hma : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].to =
          .ok (A, none) := by
        rw [ht, ctx_mem_reg (by omega) hsc]
        show Except.ok (m.rX (BitVec.ofNat 5 kp) + BitVec.ofInt 64 0, none) = _
        rw [hA]; simp
      rw [progStep_lse hf' hks hkd (nextAddr_pcAt hnd hk) has hf hma ht2 hnil, wX_pc]
      rfl)
  rw [← hk'] at hs
  exact hs

/-- The Progs of an LSE read-modify-write of family `f` (`atomPats61`) at `A`: the memory holds
the low `n` bytes of `lseG61d f` of the old word and `X kv` at `A`, `X kd` is `lseR61d f` of them,
the other X registers but `R27`, the V registers, `SP` and the flags are unchanged. -/
theorem lse_run61d (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {f : AtomF61} {n kp kv kd : Nat} (hf : f = .xchgV ∨ f = .addV ∨ f = .andV ∨ f = .orV)
    (hn : n = 8 ∨ n = 4 ∨ n = 1) (hadd : f = .addV → n ≠ 1) (hkp : kp < 31) (hkv : kv < 32)
    (hkd : kd < 31) (hp27 : kp ≠ 27) (hvd : kv ≠ kd) {j j' : Nat}
    (hvs : ManyAt2 psA j (atomPats61 f n (REG_R0 + kp) (REG_R0 + kv) (REG_R0 + kv)
      (REG_R0 + kd) 0) j')
    (m : MState) {A : BitVec 64} (hA : m.rX (BitVec.ofNat 5 kp) = A) (hnil : nilPage A = false) :
    ∃ m' : MState, PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j } m' ∧
      m'.mem = writeMem m.mem A n (BitVec.ofNat (8 * n)
        ((lseG61d f ((readMem m.mem A n).setWidth 64) (m.rX (BitVec.ofNat 5 kv))).toNat %
          2 ^ (8 * n))) ∧
      m'.x (BitVec.ofNat 5 kd) =
        lseR61d f ((readMem m.mem A n).setWidth 64) (m.rX (BitVec.ofNat 5 kv)) ∧
      (∀ q : Reg, q ≠ BitVec.ofNat 5 kd → q ≠ BitVec.ofNat 5 27 → m'.x q = m.x q) ∧
      m'.v = m.v ∧ m'.sp = m.sp ∧ m'.nzcv = m.nzcv ∧ m'.pc = pcAt text psA.toList j' := by
  rcases hf with rfl | rfl | rfl | rfl
  · -- `SWPAL Rv, (Rp), Rd`
    simp only [atomPats61] at hvs
    obtain ⟨k1, h1, hj'⟩ := hvs
    simp only [ManyAt2] at hj'
    subst hj'
    refine ⟨_, lse1_run61d (H := H) hnd hlt hret (.inl ⟨rfl, hn⟩) hkv hkp (by omega) h1 m hA hnil,
      ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · show writeMem m.mem A n _ = _
      rw [maskN_store hn]; rfl
    · show (m.wX (BitVec.ofNat 5 kd) ((readMem m.mem A n).setWidth 64)).x (BitVec.ofNat 5 kd) =
        (readMem m.mem A n).setWidth 64
      exact wX_x_self54 hkd
    · intro q h1 _
      show (m.wX (BitVec.ofNat 5 kd) _).x q = m.x q
      exact wX_x_of_ne h1
    · exact wX_fields.2.2.2
    · exact wX_fields.2.1
    · exact wX_fields.2.2.1
  · -- `LDADDAL Rv, (Rp), Rd`; `ADD Rv, Rd`
    simp only [atomPats61] at hvs
    obtain ⟨k1, h1, k2, h2, hj'⟩ := hvs
    simp only [ManyAt2] at hj'
    subst hj'
    have hn' : n = 8 ∨ n = 4 := by have := hadd rfl; omega
    obtain ⟨m1, hm1⟩ : ∃ m1 : MState, m1 =
        { m.wX (BitVec.ofNat 5 kd) ((readMem m.mem A n).setWidth 64) with
          mem := writeMem m.mem A n (BitVec.ofNat (8 * n) (ProgOp.maskN n
            (lseF .addV ((readMem m.mem A n).setWidth 64) (m.rX (BitVec.ofNat 5 kv)))).toNat) } :=
      ⟨_, rfl⟩
    have hs1 : PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j } { m1 with pc := pcAt text psA.toList k1 } := by
      rw [hm1]
      exact lse1_run61d (H := H) hnd hlt hret (.inr (.inl ⟨rfl, hn'⟩)) hkv hkp (by omega) h1 m hA
        hnil
    have hX : m1.rX (BitVec.ofNat 5 kd) = (readMem m.mem A n).setWidth 64 := by
      rw [hm1]
      show (m.wX (BitVec.ofNat 5 kd) _).rX _ = _
      exact rX_wX_self61 hkd _
    have hV : m1.rX (BitVec.ofNat 5 kv) = m.rX (BitVec.ofNat 5 kv) := by
      rw [hm1]
      show (m.wX (BitVec.ofNat 5 kd) _).rX _ = _
      exact rX_wX61 (by omega) hkv hvd _
    obtain ⟨k, hk', hs2⟩ := step1 (H := H) hnd hlt hret h2 m1
      (f := fun k => { m1.wX (BitVec.ofNat 5 kd)
          ((readMem m.mem A n).setWidth 64 + m.rX (BitVec.ofNat 5 kv)) with
        pc := pcAt text psA.toList (k + 1) })
      (fun k hk hok _ => by
        simp only [Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
        obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, hr⟩, ht⟩, -⟩, -⟩, -⟩ := hok
        have hX' : ({ m1 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kd) =
            (readMem m.mem A n).setWidth 64 := hX
        have hV' : ({ m1 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kv) =
            m.rX (BitVec.ofNat 5 kv) := hV
        rw [progStep_addTo hkv (by omega) (nextAddr_pcAt hnd hk) has hf hr ht, hX', hV', wX_pc])
    rw [← hk'] at hs2
    refine ⟨_, pstar_trans61d hs1 hs2, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · show (m1.wX _ _).mem = _
      rw [mem_wX61, hm1]
      show writeMem m.mem A n _ = _
      rw [maskN_store hn]; rfl
    · show (m1.wX _ _).x _ = _
      rw [wX_x_self54 hkd]; rfl
    · intro q h1 _
      show (m1.wX _ _).x q = m.x q
      rw [wX_x_of_ne h1, hm1]
      show (m.wX (BitVec.ofNat 5 kd) _).x q = m.x q
      exact wX_x_of_ne h1
    · show (m1.wX _ _).v = m.v
      rw [wX_fields.2.2.2, hm1]; exact wX_fields.2.2.2
    · show (m1.wX _ _).sp = m.sp
      rw [wX_fields.2.1, hm1]; exact wX_fields.2.1
    · show (m1.wX _ _).nzcv = m.nzcv
      rw [wX_fields.2.2.1, hm1]; exact wX_fields.2.2.1
  · -- `MVN Rv, R27`; `LDCLRAL R27, (Rp), Rd`
    simp only [atomPats61] at hvs
    obtain ⟨k1, h1, k2, h2, hj'⟩ := hvs
    simp only [ManyAt2] at hj'
    subst hj'
    obtain ⟨k, hk', hs1⟩ := step1 (H := H) hnd hlt hret h1 m
      (f := fun k => { m.wX (BitVec.ofNat 5 27) (~~~(m.rX (BitVec.ofNat 5 kv))) with
        pc := pcAt text psA.toList (k + 1) })
      (fun k hk hok _ => by
        simp only [Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
        obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, -⟩, -⟩, -⟩ := hok
        rw [progStep_un32 (op := .ARM64MVN) (kd := 27) rfl hkv (by omega) (nextAddr_pcAt hnd hk)
          has hf (by rw [ht]; rfl), wX_pc]
        rfl)
    rw [← hk'] at hs1
    have hA1 : (m.wX (BitVec.ofNat 5 27) (~~~(m.rX (BitVec.ofNat 5 kv)))).rX
        (BitVec.ofNat 5 kp) = A := by
      rw [rX_wX61 (by omega) (by omega) hp27]; exact hA
    have hs2 := lse1_run61d (H := H) hnd hlt hret (.inr (.inr (.inl ⟨rfl, hn⟩))) (ks := 27)
      (by omega) hkp (by omega) h2 _ hA1 hnil
    have hm1 : (m.wX (BitVec.ofNat 5 27) (~~~(m.rX (BitVec.ofNat 5 kv)))).mem = m.mem := mem_wX61
    have h27 : (m.wX (BitVec.ofNat 5 27) (~~~(m.rX (BitVec.ofNat 5 kv)))).rX (BitVec.ofNat 5 27) =
        ~~~(m.rX (BitVec.ofNat 5 kv)) := rX_wX_self61 (by omega) _
    refine ⟨_, pstar_trans61d hs1 hs2, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · show writeMem _ A n _ = _
      rw [hm1, h27, maskN_store hn]
      show writeMem m.mem A n (BitVec.ofNat (8 * n)
        (((readMem m.mem A n).setWidth 64 &&& ~~~~~~(m.rX (BitVec.ofNat 5 kv))).toNat %
          2 ^ (8 * n))) = _
      rw [BitVec.not_not]; rfl
    · show ((m.wX (BitVec.ofNat 5 27) _).wX (BitVec.ofNat 5 kd) _).x (BitVec.ofNat 5 kd) = _
      rw [wX_x_self54 hkd, hm1]; rfl
    · intro q h1 h2
      show ((m.wX (BitVec.ofNat 5 27) _).wX (BitVec.ofNat 5 kd) _).x q = m.x q
      rw [wX_x_of_ne h1, wX_x_of_ne h2]
    · show ((m.wX _ _).wX _ _).v = m.v; rw [wX_fields.2.2.2, wX_fields.2.2.2]
    · show ((m.wX _ _).wX _ _).sp = m.sp; rw [wX_fields.2.1, wX_fields.2.1]
    · show ((m.wX _ _).wX _ _).nzcv = m.nzcv; rw [wX_fields.2.2.1, wX_fields.2.2.1]
  · -- `LDORAL Rv, (Rp), Rd`
    simp only [atomPats61] at hvs
    obtain ⟨k1, h1, hj'⟩ := hvs
    simp only [ManyAt2] at hj'
    subst hj'
    refine ⟨_, lse1_run61d (H := H) hnd hlt hret (.inr (.inr (.inr ⟨rfl, hn⟩))) hkv hkp (by omega)
      h1 m hA hnil, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · show writeMem m.mem A n _ = _
      rw [maskN_store hn]; rfl
    · show (m.wX (BitVec.ofNat 5 kd) ((readMem m.mem A n).setWidth 64)).x (BitVec.ofNat 5 kd) =
        (readMem m.mem A n).setWidth 64
      exact wX_x_self54 hkd
    · intro q h1 _
      show (m.wX (BitVec.ofNat 5 kd) _).x q = m.x q
      exact wX_x_of_ne h1
    · exact wX_fields.2.2.2
    · exact wX_fields.2.1
    · exact wX_fields.2.2.1

/-- The Progs of an LSE compare-and-swap (`atomPats61 .casV`) at `A`: when the zero-extended `n`
bytes at `A` are `maskN n (X ko)`, the low `n` bytes of `X kn` are stored there and `X kd` is 1,
else the memory stays and `X kd` is 0; the other X registers but `R27`, the V registers and `SP`
are unchanged. -/
theorem casV_run61d (hnd : (psA.toList.map (·.id)).Nodup)
    (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {n kp ko kn kd : Nat} (hn : n = 8 ∨ n = 4) (hkp : kp < 31) (hko : ko < 32) (hkn : kn < 32)
    (hkd : kd < 31) (hp27 : kp ≠ 27) (ho27 : ko ≠ 27) (hn27 : kn ≠ 27) {j j' : Nat}
    (hvs : ManyAt2 psA j (atomPats61 .casV n (REG_R0 + kp) (REG_R0 + ko) (REG_R0 + kn)
      (REG_R0 + kd) 0) j')
    (m : MState) {A : BitVec 64} (hA : m.rX (BitVec.ofNat 5 kp) = A) (hnil : nilPage A = false) :
    ∃ m' : MState, PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j } m' ∧
      m'.mem = (if (readMem m.mem A n).setWidth 64 == ProgOp.maskN n (m.rX (BitVec.ofNat 5 ko))
        then writeMem m.mem A n
          (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 kn)).toNat % 2 ^ (8 * n)))
        else m.mem) ∧
      m'.x (BitVec.ofNat 5 kd) =
        (if (readMem m.mem A n).setWidth 64 == ProgOp.maskN n (m.rX (BitVec.ofNat 5 ko))
          then 1 else 0) ∧
      (∀ q : Reg, q ≠ BitVec.ofNat 5 kd → q ≠ BitVec.ofNat 5 27 → m'.x q = m.x q) ∧
      m'.v = m.v ∧ m'.sp = m.sp ∧ m'.pc = pcAt text psA.toList j' := by
  simp only [atomPats61] at hvs
  obtain ⟨k1, h1, k2, h2, k3, h3, k4, h4, hj'⟩ := hvs
  simp only [ManyAt2] at hj'
  subst hj'
  -- `MOVD`/`MOVW Ro, R27`
  obtain ⟨W, hW, hs1⟩ : ∃ W : BitVec 64,
      ProgOp.maskN n W = ProgOp.maskN n (m.rX (BitVec.ofNat 5 ko)) ∧
      PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j }
        { m.wX (BitVec.ofNat 5 27) W with pc := pcAt text psA.toList k1 } := by
    rcases hn with rfl | rfl
    · refine ⟨m.rX (BitVec.ofNat 5 ko), rfl, ?_⟩
      obtain ⟨k, hk', hs⟩ := step1 (H := H) hnd hlt hret h1 m
        (f := fun k => { m.wX (BitVec.ofNat 5 27) (m.rX (BitVec.ofNat 5 ko)) with
          pc := pcAt text psA.toList (k + 1) })
        (fun k hk hok _ => by
          simp only [Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq, ↓reduceIte] at hok
          obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, -⟩, -⟩, -⟩ := hok
          rw [progStep_movReg (kd := 27) hko (by omega) (nextAddr_pcAt hnd hk) has hf
            (by rw [ht]; rfl), wX_pc]
          rfl)
      rw [← hk'] at hs
      exact hs
    · refine ⟨ProgOp.sextTo64 4 (m.rX (BitVec.ofNat 5 ko)), maskN_sext61d _, ?_⟩
      obtain ⟨k, hk', hs⟩ := step1 (H := H) hnd hlt hret h1 m
        (f := fun k => { m.wX (BitVec.ofNat 5 27)
            (ProgOp.sextTo64 4 (m.rX (BitVec.ofNat 5 ko))) with
          pc := pcAt text psA.toList (k + 1) })
        (fun k hk hok _ => by
          simp only [Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
          obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, -⟩, -⟩, -⟩ := hok
          rw [progStep_ext (n := 4) (sg := true) (kd := 27) hko (by omega) (nextAddr_pcAt hnd hk)
            (by rw [has]; rfl) hf (by rw [ht]; rfl), wX_pc]
          rfl)
      rw [← hk'] at hs
      exact hs
  -- `CASAL R27, (Rp), Rn`
  obtain ⟨m2, hm2⟩ : ∃ m2 : MState, m2 =
      if (readMem m.mem A n).setWidth 64 == ProgOp.maskN n (m.rX (BitVec.ofNat 5 ko)) then
        { (m.wX (BitVec.ofNat 5 27) W).wX (BitVec.ofNat 5 27) ((readMem m.mem A n).setWidth 64) with
          mem := writeMem m.mem A n
            (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 kn)).toNat % 2 ^ (8 * n))) }
      else (m.wX (BitVec.ofNat 5 27) W).wX (BitVec.ofNat 5 27) ((readMem m.mem A n).setWidth 64) :=
    ⟨_, rfl⟩
  obtain ⟨k, hk', hs2⟩ := step1 (H := H) hnd hlt hret h2 (m.wX (BitVec.ofNat 5 27) W)
    (f := fun k => { m2 with pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      simp only [lsePat, Shape.okT, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, ht2⟩ := hok
      have hma : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m.wX (BitVec.ofNat 5 27) W with pc := pcAt text psA.toList k } psA.toList[k]).mem
            psA.toList[k].to = .ok (A, none) := by
        rw [ht, ctx_mem_reg (by omega) hsc]
        show Except.ok ((m.wX (BitVec.ofNat 5 27) W).rX (BitVec.ofNat 5 kp) +
          BitVec.ofInt 64 0, none) = _
        rw [rX_wX61 (by omega) (by omega) hp27, hA]; simp
      have hmem : ({ m.wX (BitVec.ofNat 5 27) W with pc := pcAt text psA.toList k } : MState).mem =
          m.mem := by
        show (m.wX (BitVec.ofNat 5 27) W).mem = m.mem
        exact mem_wX61
      have h27 : ({ m.wX (BitVec.ofNat 5 27) W with pc := pcAt text psA.toList k } : MState).rX
          (BitVec.ofNat 5 27) = W := by
        show (m.wX (BitVec.ofNat 5 27) W).rX (BitVec.ofNat 5 27) = W
        exact rX_wX_self61 (by omega) W
      have hXn : ({ m.wX (BitVec.ofNat 5 27) W with pc := pcAt text psA.toList k } : MState).rX
          (BitVec.ofNat 5 kn) = m.rX (BitVec.ofNat 5 kn) := by
        show (m.wX (BitVec.ofNat 5 27) W).rX (BitVec.ofNat 5 kn) = _
        exact rX_wX61 (by omega) hkn hn27 W
      rw [progStep_casal hn (ks := 27) (by omega) hkn (nextAddr_pcAt hnd hk) has (by rw [hf]; rfl)
        hma ht2 hnil, hmem, h27, hXn, hW, wX_pc, hm2]
      cases (readMem m.mem A n).setWidth 64 == ProgOp.maskN n (m.rX (BitVec.ofNat 5 ko)) <;>
        simp only [Bool.false_eq_true, ↓reduceIte] <;> rfl)
  rw [← hk'] at hs2
  have h2rX : ∀ r, m2.rX r =
      ((m.wX (BitVec.ofNat 5 27) W).wX (BitVec.ofNat 5 27)
        ((readMem m.mem A n).setWidth 64)).rX r := by
    intro r; rw [hm2]; split <;> rfl
  have h2x : ∀ q, m2.x q =
      ((m.wX (BitVec.ofNat 5 27) W).wX (BitVec.ofNat 5 27)
        ((readMem m.mem A n).setWidth 64)).x q := by
    intro q; rw [hm2]; split <;> rfl
  have h2v : m2.v = m.v := by
    rw [hm2]
    split <;> (show ((m.wX _ _).wX _ _).v = m.v; rw [wX_fields.2.2.2, wX_fields.2.2.2])
  have h2sp : m2.sp = m.sp := by
    rw [hm2]
    split <;> (show ((m.wX _ _).wX _ _).sp = m.sp; rw [wX_fields.2.1, wX_fields.2.1])
  have h2mem : m2.mem =
      (if (readMem m.mem A n).setWidth 64 == ProgOp.maskN n (m.rX (BitVec.ofNat 5 ko))
        then writeMem m.mem A n
          (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 kn)).toNat % 2 ^ (8 * n)))
        else m.mem) := by
    rw [hm2]
    cases (readMem m.mem A n).setWidth 64 == ProgOp.maskN n (m.rX (BitVec.ofNat 5 ko)) <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [mem_wX61, mem_wX61]
  have h27' : m2.rX (BitVec.ofNat 5 27) = (readMem m.mem A n).setWidth 64 := by
    rw [h2rX]; exact rX_wX_self61 (by omega) _
  have hro' : m2.rX (BitVec.ofNat 5 ko) = m.rX (BitVec.ofNat 5 ko) := by
    rw [h2rX, rX_wX61 (by omega) hko ho27, rX_wX61 (by omega) hko ho27]
  -- `CMP`/`CMPW Ro, R27`
  obtain ⟨F, hF, hs3⟩ : ∃ F : Flags,
      F.z = ((readMem m.mem A n).setWidth 64 == ProgOp.maskN n (m.rX (BitVec.ofNat 5 ko))) ∧
      PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m2 with pc := pcAt text psA.toList k2 }
        { ({ m2 with nzcv := F } : MState) with pc := pcAt text psA.toList k3 } := by
    rcases hn with rfl | rfl
    · refine ⟨(Arm64.subFlags ((readMem m.mem A 8).setWidth 64) (m.rX (BitVec.ofNat 5 ko))).2,
        by rw [subFlags_z64]; rfl, ?_⟩
      obtain ⟨k, hk', hs⟩ := step1 (H := H) hnd hlt hret h3 m2
        (f := fun k => { ({ m2 with nzcv := (Arm64.subFlags ((readMem m.mem A 8).setWidth 64)
          (m.rX (BitVec.ofNat 5 ko))).2 } : MState) with pc := pcAt text psA.toList (k + 1) })
        (fun k hk hok _ => by
          simp only [cmp61Pat, Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq,
            ↓reduceIte] at hok
          obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, hr⟩, -⟩, -⟩, -⟩, -⟩ := hok
          have h27k : ({ m2 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 27) =
              (readMem m.mem A 8).setWidth 64 := h27'
          have hy : ProgCtx.src ⟨Link.byId sym text az ez psA.toList,
              { m2 with pc := pcAt text psA.toList k }, psA.toList[k]⟩ true psA.toList[k].from_ =
              .ok (m.rX (BitVec.ofNat 5 ko)) := by
            rw [hf]; exact (ctx_src_reg hko).trans (congrArg Except.ok hro')
          rw [progStep_cmp (kn := 27) (by omega) (nextAddr_pcAt hnd hk) has hy (by rw [hr]; rfl),
            h27k])
      rw [← hk'] at hs
      exact hs
    · refine ⟨(Arm64.subFlags (((readMem m.mem A 4).setWidth 64).setWidth 32)
        ((m.rX (BitVec.ofNat 5 ko)).setWidth 32)).2,
        by rw [subFlags_z32]; exact (beq_maskN61d (.inr rfl) _ _).symm, ?_⟩
      obtain ⟨k, hk', hs⟩ := step1 (H := H) hnd hlt hret h3 m2
        (f := fun k => { ({ m2 with nzcv := (Arm64.subFlags
          (((readMem m.mem A 4).setWidth 64).setWidth 32)
          ((m.rX (BitVec.ofNat 5 ko)).setWidth 32)).2 } : MState) with
            pc := pcAt text psA.toList (k + 1) })
        (fun k hk hok _ => by
          simp only [cmp61Pat, Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
          obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, hr⟩, -⟩, -⟩, -⟩, -⟩ := hok
          have h27k : ({ m2 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 27) =
              (readMem m.mem A 4).setWidth 64 := h27'
          have hrok : ({ m2 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 ko) =
              m.rX (BitVec.ofNat 5 ko) := hro'
          rw [progStep_cmpwReg (kn := 27) (km := ko) (by omega) hko (nextAddr_pcAt hnd hk) has hf
            (by rw [hr]; rfl), h27k, hrok])
      rw [← hk'] at hs
      exact hs
  -- `CSET EQ, Rd`
  obtain ⟨k, hk', hs4⟩ := step1 (H := H) hnd hlt hret h4 { m2 with nzcv := F }
    (f := fun k => { ({ m2 with nzcv := F } : MState).wX (BitVec.ofNat 5 kd)
      (if F.z then 1 else 0) with pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      simp only [csetEqPat, Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, -⟩, -⟩, -⟩ := hok
      rw [progStep_cset (cc := SPOP_EQ) (by omega) (nextAddr_pcAt hnd hk) has hf
        ⟨Int.le_refl _, by omega⟩ ht, wX_pc]
      rfl)
  rw [← hk'] at hs4
  refine ⟨_, pstar_trans61d hs1 (pstar_trans61d hs2 (pstar_trans61d hs3 hs4)), ?_, ?_, ?_, ?_, ?_,
    rfl⟩
  · show (({ m2 with nzcv := F } : MState).wX _ _).mem = _
    rw [mem_wX61]; exact h2mem
  · show (({ m2 with nzcv := F } : MState).wX _ _).x _ = _
    rw [wX_x_self54 hkd, hF]
  · intro q h1 h2
    show (({ m2 with nzcv := F } : MState).wX _ _).x q = m.x q
    rw [wX_x_of_ne h1]
    show m2.x q = m.x q
    rw [h2x, wX_x_of_ne h2, wX_x_of_ne h2]
  · show (({ m2 with nzcv := F } : MState).wX _ _).v = m.v
    rw [wX_fields.2.2.2]; exact h2v
  · show (({ m2 with nzcv := F } : MState).wX _ _).sp = m.sp
    rw [wX_fields.2.1]; exact h2sp

end Runs

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K : Nat → Option Nat}

/-- `LoweredAtomic{Exchange,Add,And,Or}*Variant p x mem`: the LSE instruction (with `ADD` after an
add, `MVN` before an and) loads the location's old value, stores `Atomic.step`'s new value and
leaves the result (the sum for an add, else the old value) in `Rd`. -/
theorem g61_lse (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {f : AtomF61} {n : Nat} {t0 : Ty} {rp rv rd : Int} {r : Nat}
    (hop : atom61? v.op = some (f, n)) (hf : f = .xchgV ∨ f = .addV ∨ f = .andV ∨ f = .orV)
    (hsz3 : v.args.size = 3) (hty : lc.ty v.id = .tuple [t0, .mem]) (hc0 : cls t0 = some (8 * n))
    (hap : argObj lc v 0 = .ok (64, rp)) (hpr : rp ≠ r27A) (hpz : rp ≠ ARM64.REGZERO)
    (hav : argObj lc v 1 = .ok (8 * n, rv)) (hvr : rv ≠ r27A) (hma : memArg lc v 2 = .ok ())
    (hh : lc.home v.id = some (.pair (some r) none)) (hrz : r ≠ zeroReg) (hd : destOK r = true)
    (hor : objOf? r = some rd) (hdp : rd ≠ rp) (hdv : rd ≠ rv)
    (htemp : (lc.temps[v.id]?).join = none)
    (hvs : ManyAt2 psA j (atomPats61 f n rp rv rv rd 0) j') (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kSet K r (some (8 * n))) s' osp ∧
      SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨hnp, -, -, -, -, -, -, -, -, -, -, -, hn, hwb, hadd, -⟩ := atom61?_facts hop
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hap
  obtain ⟨kp, hkp, rfl, hkkp⟩ := objOf?_some hor0
  have hkp31 := objOf?_lt31 hkp hkkp hpz
  have hp27 : kp ≠ 27 := fun h => hpr (by rw [h]; rfl)
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hav
  obtain ⟨kv, hkv, rfl, hkkv⟩ := objOf?_some hor1
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨kd, hkd, rfl, hkkd⟩ := objOf?_some hor
  obtain ⟨hkd31, hk27⟩ : kd < 31 ∧ kd ≠ 27 := by
    rcases hkkd with ⟨h, -⟩ | ⟨h, ho⟩
    · exact absurd h hrz
    · exact ⟨h, fun he => objX?_ne27 ho (by rw [he])⟩
  have hvd : kv ≠ kd := fun h => hdv (by rw [h])
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkp
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkv
  have hf1 : f ≠ .cas := by rintro rfl; rcases hf with h | h | h | h <;> cases h
  have hf2 : f ≠ .casV := by rintro rfl; rcases hf with h | h | h | h <;> cases h
  obtain ⟨x, y, p, mm', hx, hy, hpw, hal, hw, rfl⟩ := stepLoc_rmw61 hl hop hf1 hf2
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hx] at hX; cases hX
  rw [hy] at hY; cases hY
  have hsz' : (Ty.int (widthN n)).size = n := by rcases hn with rfl | rfl | rfl <;> rfl
  rw [hsz'] at hal
  have hcan : mm.canWrite p n = true := by
    have := canWrite_of_write hw (by rw [GoFV.SSA.Sem.encode_size, hsz']; omega)
    rwa [GoFV.SSA.Sem.encode_size, hsz'] at this
  obtain ⟨a, hpa, haeq, hnil⟩ :=
    addr_rel hA hMI hxv hxf (addr_asPtrWord hpw) (by omega : 0 < n) (.inl hcan)
  have haeq' : m.rX (BitVec.ofNat 5 kp) = a + p.off := by simpa using haeq
  have hrd := read_of_canWrite hcan (by omega)
  have hO := old_rel61 hA hMI hn hpa hal hrd
  have hres := res_rel61 hA hMI hn hc0 hpa hal hrd
  obtain ⟨z, hz, hzf, hzv⟩ := lse_store61d hA hf hn hO hyv hyf
  obtain ⟨rr, hrr, hrrv⟩ := lse_res61d hA hf hn hc0 hO hyv hyf hres
  have hfz : Fits (widthN n).bits z := by rw [widthN_bits hn]; exact hzf
  rw [hz, encode_storeBytes hfz, hwb] at hw
  obtain ⟨hM', hk', hsep', hP⟩ := atom_store61 hA hMI hk0 hsep0 hn hpa hzv hzf hw
  obtain ⟨m', hrun, hmem', hxd, hxo, hv', hsp', hfl', hpc'⟩ := lse_run61d (H := H) F.nodup F.lt
    F.ret hf hn hadd hkp31 hkv hkd31 hp27 hvd hvs m haeq' hnil
  rw [pc_eta hm hj] at hrun
  rw [hrr]
  simp only [Atomic.result]
  rw [hty, retypeL_pair, retypeL_mem, write_atom61 hh hty (by rw [hc0]; rfl)]
  obtain ⟨hlm, hcore, hsl⟩ := atom_finish (m' := m') hF hsz hm hinv hsi hkd hor hd hrz
    (fits_retypeL hc0 _) (by rw [hxd]; exact hrrv) (by rw [hmem']; exact hM') hk' hsep'
    (fun y hy => by rw [hmem']; exact hP y hy) (fun t ht => by rw [htemp] at ht; cases ht)
    (fun q h1 h2 _ => hxo q h1 h2) hv' hsp' (fun _ => hfl') (hpc'.trans hj'.symm)
  exact ⟨_, hrun, hlm, hcore, hsl⟩

/-- `LoweredAtomicCas{64,32}Variant p old new mem`: `CASAL` stores `new` exactly when the location
holds `old` (the low bits of `Ro`, moved to `R27`), and `CMP`/`CSET` leave that outcome as 0/1 in
`Rd`, `runLoc`'s boolean. -/
theorem g61_casV (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} {t0 : Ty} {rp ro rn rd : Int} {r : Nat}
    (hop : atom61? v.op = some (.casV, n)) (htemp : (lc.temps[v.id]?).join = none)
    (hsz4 : v.args.size = 4) (hty : lc.ty v.id = .tuple [t0, .mem]) (hc0 : cls t0 = some 1)
    (hap : argObj lc v 0 = .ok (64, rp)) (hpr : rp ≠ r27A) (hpz : rp ≠ ARM64.REGZERO)
    (hao : argObj lc v 1 = .ok (8 * n, ro)) (hor27 : ro ≠ r27A)
    (han : argObj lc v 2 = .ok (8 * n, rn)) (hnr : rn ≠ r27A) (hma : memArg lc v 3 = .ok ())
    (hh : lc.home v.id = some (.pair (some r) none)) (hrz : r ≠ zeroReg) (hd : destOK r = true)
    (hor : objOf? r = some rd)
    (hvs : ManyAt2 psA j (atomPats61 .casV n rp ro rn rd 0) j') (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kSet K r (some 1)) s' osp ∧
      SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨hnp, -, -, -, -, -, -, -, hcf, -, -, -, hn, hwb, -, hn1, -⟩ := atom61?_facts hop
  have hn' : n = 8 ∨ n = 4 := by have := hn1 (.inr (.inl rfl)); omega
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hap
  obtain ⟨kp, hkp, rfl, hkkp⟩ := objOf?_some hor0
  have hkp31 := objOf?_lt31 hkp hkkp hpz
  have hp27 : kp ≠ 27 := fun h => hpr (by rw [h]; rfl)
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hao
  obtain ⟨ko, hko, rfl, hkko⟩ := objOf?_some hor1
  have ho27 : ko ≠ 27 := fun h => hor27 (by rw [h]; rfl)
  obtain ⟨a2, r2, ha2, hah2, hor2, hca2⟩ := argObj_spec han
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor2
  have hn27 : kn ≠ 27 := fun h => hnr (by rw [h]; rfl)
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨kd, hkd, rfl, hkkd⟩ := objOf?_some hor
  obtain ⟨hkd31, hk27⟩ : kd < 31 ∧ kd ≠ 27 := by
    rcases hkkd with ⟨h, -⟩ | ⟨h, ho⟩
    · exact absurd h hrz
    · exact ⟨h, fun he => objX?_ne27 ho (by rw [he])⟩
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkp
  obtain ⟨Yo, hYo, hyov, hyof⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkko
  obtain ⟨Yn, hYn, hynv, hynf⟩ :=
    arg_rel hA hl hm hinv hah2 hca2 (kread_arg hR hnp ha2 hah2 hca2) hkkn
  obtain ⟨x, yo, yn, p, cur, old, hx, hyo, hyn, hpw, hal, hcur, hold, hcase⟩ :=
    stepLoc_cas61 hl hop (.inr rfl) (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hx] at hX; cases hX
  rw [hyo] at hYo; cases hYo
  rw [hyn] at hYn; cases hYn
  rw [hwb] at hal
  obtain ⟨bs, hbs⟩ := read_of_load61d hcur
  rw [hwb] at hbs
  obtain ⟨a, hpa, haeq, hnil⟩ :=
    addr_rel hA hMI hxv hxf (addr_asPtrWord hpw) (by omega : 0 < n) (.inr (by rw [hbs]; rfl))
  have haeq' : m.rX (BitVec.ofNat 5 kp) = a + p.off := by simpa using haeq
  have hcur' := old_rel61 hA hMI hn hpa hal ⟨bs, hbs⟩ cur hcur
  have hold' := fit_asInt61 hA hyov (by rw [widthN_bits hn]; exact hyof) old hold
  -- the machine's comparison is `runLoc`'s
  have heqb : ((readMem m.mem (a + p.off) n).setWidth 64 ==
      ProgOp.maskN n (m.rX (BitVec.ofNat 5 ko))) = decide (cur = old) := by
    rw [beq_maskN61d hn', hcur', hold']
    cases h : decide (cur = old)
    · simp only [decide_eq_false_iff_not] at h; simp [h]
    · simp only [decide_eq_true_eq] at h; simp [h]
  obtain ⟨m', hrun, hmem', hxd, hxo, hv', hsp', hpc'⟩ := casV_run61d (H := H) F.nodup F.lt F.ret
    hn' hkp31 hko hkn hkd31 hp27 ho27 hn27 hvs m haeq' hnil
  rw [pc_eta hm hj] at hrun
  rw [heqb] at hmem' hxd
  have hcl : v.op.clobberFlags = true := by rw [hcf]; rfl
  rcases hcase with ⟨heq, mm', hw, rfl⟩ | ⟨hne, rfl⟩
  · -- the location held `old`: `new` stored, `true`
    simp only [decide_eq_true heq, ↓reduceIte] at hmem' hxd
    have hfn : Fits (widthN n).bits Yn := by rw [widthN_bits hn]; exact hynf
    rw [encode_storeBytes hfn, hwb] at hw
    obtain ⟨hM', hk', hsep', hP⟩ := atom_store61 hA hMI hk0 hsep0 hn hpa hynv hynf hw
    rw [hty, retypeL_pair, retypeL_mem, write_atom61 hh hty (by rw [hc0]; rfl)]
    have hb : ValRel E.ι ((Val.bool true).retypeL t0) 1 :=
      valRel_retypeL hA hc0 (show Fits 1 (Val.bool true) from rfl)
        (show ValRel E.ι (Val.bool true) 1 from rfl)
    obtain ⟨hlm, hcore, hsl⟩ := atom_finish (m' := m') hF hsz hm hinv hsi hkd hor hd hrz
      (fits_retypeL hc0 _) (by rw [hxd]; exact hb)
      (by rw [hmem']; exact hM') hk' hsep' (fun y hy => by rw [hmem']; exact hP y hy)
      (fun t ht => by rw [htemp] at ht; cases ht) (fun q h1 h2 _ => hxo q h1 h2) hv' hsp'
      (fun h => absurd (hcl.symm.trans h) nofun) (hpc'.trans hj'.symm)
    exact ⟨_, hrun, hlm, hcore, hsl⟩
  · -- it did not: the memory stays, `false`
    simp only [decide_eq_false hne, Bool.false_eq_true, ↓reduceIte] at hmem' hxd
    rw [hty, retypeL_pair, retypeL_mem, write_atom61 hh hty (by rw [hc0]; rfl)]
    have hb : ValRel E.ι ((Val.bool false).retypeL t0) 0 :=
      valRel_retypeL hA hc0 (show Fits 1 (Val.bool false) from rfl)
        (show ValRel E.ι (Val.bool false) 0 from rfl)
    obtain ⟨hlm, hcore, hsl⟩ := atom_finish (m' := m') hF hsz hm hinv hsi hkd hor hd hrz
      (fits_retypeL hc0 _) (by rw [hxd]; exact hb)
      (by rw [hmem']; exact hMI) hk0 hsep0 (fun y _ => by rw [hmem'])
      (fun t ht => by rw [htemp] at ht; cases ht) (fun q h1 h2 _ => hxo q h1 h2) hv' hsp'
      (fun h => absurd (hcl.symm.trans h) nofun) (hpc'.trans hj'.symm)
    exact ⟨_, hrun, hlm, hcore, hsl⟩

end Cases

end GoFV.Proof.Gen
