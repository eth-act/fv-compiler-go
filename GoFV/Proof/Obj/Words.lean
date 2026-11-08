import GoFV.Proof.Obj.Insn
import GoFV.Proof.Obj.Link
import GoFV.SSA.Sem.LocMatch

/-!
# The words of a Prog run as `symWords` says (`GoFV/Asm/CheckObj.lean`)

`symWords_sound`: if `symWords` accepts the `n + 1` words at offset `o` with effect `σ'` and
control `mc`, then from a state at `base + o` that the starting effect describes, the linked code
runs (`MStar`, one machine step per word) to a state that `σ'` describes, with the PC (and for a
call `X30`) where `mc` goes from the last word at `o + 4 n`. Units (`symUnit`): a plain word
(`symInsn_sound`), a `BL`/`B` of `R_CALLARM64` (`decode_call`), the two words of `R_ADDRARM64`
(`decode_adrp`, `decode_addLo`) and of `R_ARM64_PCREL_LDST*` (`decode_adrp`, `decode_ldstLo`,
`symAccess_exec`).
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.SSA.Sem (MStep MStar)

/-! ## Effects grow -/

/-- `σ'` performs every load and store of `σ`. -/
def SymLe (σ σ' : Sym) : Prop :=
  (∀ x ∈ σ.loads, x ∈ σ'.loads) ∧ (∀ x ∈ σ.stores, x ∈ σ'.stores)

theorem SymLe.refl (σ : Sym) : SymLe σ σ := ⟨fun _ h => h, fun _ h => h⟩

theorem SymLe.trans {σ σ' σ'' : Sym} (h : SymLe σ σ') (h' : SymLe σ' σ'') : SymLe σ σ'' :=
  ⟨fun x hx => h'.1 x (h.1 x hx), fun x hx => h'.2 x (h.2 x hx)⟩

theorem NoNil.mono {c : Ctx} {σ σ' : Sym} (h : NoNil c σ') (hle : SymLe σ σ') : NoNil c σ :=
  ⟨fun a n hx => h.1 a n (hle.1 _ hx), fun a n v hx => h.2 a n v (hle.2 _ hx)⟩

theorem SymLe.of_wX (σ : Sym) (r : Nat) (v : Ex) : SymLe σ (σ.wX r v) := by
  unfold Sym.wX; split <;> exact ⟨fun _ h => h, fun _ h => h⟩

theorem SymLe.of_wXsp (σ : Sym) (r : Nat) (v : Ex) : SymLe σ (σ.wXsp r v) := by
  unfold Sym.wXsp; split
  · exact ⟨fun _ h => h, fun _ h => h⟩
  · exact SymLe.of_wX σ r v

theorem SymLe.wX {σ σ' : Sym} (h : SymLe σ σ') (r : Nat) (v : Ex) : SymLe σ (σ'.wX r v) :=
  h.trans (SymLe.of_wX σ' r v)

theorem SymLe.wXsp {σ σ' : Sym} (h : SymLe σ σ') (r : Nat) (v : Ex) : SymLe σ (σ'.wXsp r v) :=
  h.trans (SymLe.of_wXsp σ' r v)

theorem SymLe.of_load {σ σ' : Sym} {a v : Ex} {n : Nat} (h : σ.load a n = .ok (σ', v)) : SymLe σ σ' := by
  unfold Sym.load at h
  split at h
  · cases h; exact ⟨fun _ hx => List.mem_cons_of_mem _ hx, fun _ hx => hx⟩
  · cases h

theorem SymLe.of_store (σ : Sym) (a : Ex) (n : Nat) (v : Ex) : SymLe σ (σ.store a n v) :=
  ⟨fun _ hx => hx, fun _ hx => List.mem_append_left _ hx⟩

theorem symAccess_le {σ σ' : Sym} {size opc : BitVec 2} {rt : Nat} {a : Ex}
    (h : symAccess σ size opc rt a = .ok σ') : SymLe σ σ' := symAccess_mono h

theorem symInsn_le {i : Insn} {o : Nat} {σ σ' : Sym} {mc : MCtl}
    (h : symInsn i o σ = .ok (σ', mc)) : SymLe σ σ' := symInsn_mono h

/-! ## Machine steps -/

variable {base : BitVec 64} {sym : Nat → BitVec 64} {t : ByteArray} {rs : List Reloc}
  {code : Code} {H : Hooks} {retM : BitVec 64}

theorem mstar_trans {s s' s'' : MState} (h : MStar H code retM s s') (h' : MStar H code retM s' s'') :
    MStar H code retM s s'' := by
  induction h' with
  | refl => exact h
  | tail _ hs ih => exact .tail ih hs

theorem mstar_single {s s' : MState} (h : MStep H code retM s s') : MStar H code retM s s' :=
  .tail .refl h

/-- One word executed at `base + o`. -/
theorem mstep_word {o : Nat} {w : BitVec 32} {i : Insn} {tm tm' : MState}
    (hc : code (base + BitVec.ofNat 64 o) = some w) (hd : decode w = some i)
    (he : exec i tm = .ok tm') (hpc : tm.pc = base + BitVec.ofNat 64 o) (hret : code retM = none) :
    MStep H code retM tm tm' := by
  refine .exec ?_ ?_ ?_
  · intro h; rw [hpc] at h; rw [← h, hc] at hret; cases hret
  · rw [hpc, hc]; simp
  · simp [step, hpc, hc, hd, he]

theorem at_succ (base : BitVec 64) (o k : Nat) :
    base + BitVec.ofNat 64 o + BitVec.ofNat 64 k = at_ base ((o + k : Nat) : Int) := by
  simp only [at_, BitVec.ofInt_natCast, BitVec.add_assoc, BitVec.ofNat_add]

theorem at_nat (base : BitVec 64) (o : Nat) : base + BitVec.ofNat 64 o = at_ base (o : Int) := by
  simp [at_]

/-- `at_succ` with the offset in any form. -/
private theorem at_close (base : BitVec 64) (o k : Nat) (j : Int) (hj : j = ((o + k : Nat) : Int)) :
    base + BitVec.ofNat 64 o + BitVec.ofNat 64 k = at_ base j := by
  subst hj; exact at_succ base o k

theorem callLink?_eq {i : Insn} {link : Bool} (h : callLink? i = some link) : i = .b link 0 := by
  cases i <;> simp [callLink?] at h
  rename_i l imm; obtain ⟨rfl, rfl⟩ := h; rfl

theorem adrpRd?_eq {i : Insn} {rd : Reg} (h : adrpRd? i = some rd) : i = .adr true 0 rd ∧ rd ≠ 31 := by
  cases i <;> simp [adrpRd?] at h
  obtain ⟨⟨rfl, rfl, h31⟩, rfl⟩ := h; exact ⟨rfl, h31⟩

theorem addLo?_eq {i : Insn} {rd rd2 : Reg} (h : addLo? rd i = some rd2) :
    i = .addSubImm true false false false 0 rd rd2 := by
  cases i <;> simp [addLo?] at h
  obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := h; rfl

theorem ldstLo?_eq {i : Insn} {rd : Reg} {sc : Nat} {q : BitVec 2 × BitVec 2 × Reg}
    (h : ldstLo? rd sc i = some q) :
    i = .ldst q.1 false q.2.1 (.uimm 0) rd q.2.2 ∧ q.1.toNat = sc := by
  cases i <;> simp [ldstLo?] at h
  rename_i size vec opc mode rn rt
  cases mode <;> simp at h
  obtain ⟨⟨rfl, rfl, rfl, hsc⟩, rfl⟩ := h; exact ⟨rfl, hsc⟩

private theorem wd_bind_ok {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {b : β}
    (h : (x >>= g) = .ok b) : ∃ a, x = .ok a ∧ g a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A `throw` is not `.ok` (stated over a variable message, so the kernel never unfolds it). -/
private theorem wd_throw {ε α : Type} {e : ε} {b : α} (h : (throw e : Except ε α) = .ok b) :
    False := nomatch h

private theorem wd_ok3 {ε α β γ : Type} {a a' : α} {b b' : β} {c c' : γ}
    (h : (pure (a, b, c) : Except ε (α × β × γ)) = .ok (a', b', c')) : a = a' ∧ b = b' ∧ c = c' := by
  cases h; exact ⟨rfl, rfl, rfl⟩

/-- What `symUnit` accepted. -/
theorem symUnit_inv {n o : Nat} {σ σ' : Sym} {mc : MCtl} {used : Nat}
    (h : symUnit t rs n o σ = .ok (σ', mc, used)) :
    o + 4 ≤ t.size ∧ o % 4 = 0 ∧ ∃ i, decode (wordAt t o) = some i ∧
    ((relocAt rs o = none ∧ covering rs o = [] ∧ symInsn i o σ = .ok (σ', mc) ∧ used = 1) ∨
     (∃ r y link, relocAt rs o = some r ∧ r.sym = some y ∧ isCallReloc r.type = true ∧
       i = .b link 0 ∧ σ' = σ ∧ used = 1 ∧ mc = (if link then .call y r.add else .jmpSym y r.add)) ∨
     (∃ r y rd i2, relocAt rs o = some r ∧ r.sym = some y ∧ isCallReloc r.type = false ∧
       o + 8 ≤ t.size ∧ covering rs (o + 4) = [r] ∧ i = .adr true 0 rd ∧ rd ≠ 31 ∧
       decode (wordAt t (o + 4)) = some i2 ∧ mc = .fall ∧ used = 2 ∧
       ((r.type = "R_ADDRARM64" ∧ ∃ rd2, i2 = .addSubImm true false false false 0 rd rd2 ∧
          σ' = (σ.wX rd.toNat (.page (relTgt y r))).wXsp rd2.toNat (relTgt y r)) ∨
        (∃ size opc rt, ldstScale r.type = some size.toNat ∧ i2 = .ldst size false opc (.uimm 0) rd rt ∧
          symAccess (σ.wX rd.toNat (.page (relTgt y r))) size opc rt.toNat (relTgt y r) = .ok σ')))) := by
  unfold symUnit at h
  by_cases h1 : (decide (o + 4 > t.size) || o % 4 != 0) = true
  · simp only [h1, ↓reduceIte] at h; exact (wd_throw h).elim
  simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
  have h1' : o + 4 ≤ t.size ∧ o % 4 = 0 := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at h1
    omega
  refine ⟨h1'.1, h1'.2, ?_⟩
  cases hd : decode (wordAt t o) with
  | none => simp only [hd] at h; exact (wd_throw h).elim
  | some i =>
  simp only [hd] at h
  refine ⟨i, rfl, ?_⟩
  cases hr : relocAt rs o with
  | none =>
    simp only [hr] at h
    by_cases hc : (!(covering rs o).isEmpty) = true
    · simp only [hc, ↓reduceIte] at h; exact (wd_throw h).elim
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨⟨σa, ca⟩, hs, h⟩ := wd_bind_ok h
    obtain ⟨rfl, rfl, rfl⟩ := wd_ok3 h
    left
    refine ⟨rfl, ?_, hs, rfl⟩
    simpa using hc
  | some r =>
  simp only [hr] at h
  unfold symUnitRel at h
  cases hy : r.sym with
  | none => simp only [hy] at h; exact (wd_throw h).elim
  | some y =>
  simp only [hy] at h
  right
  by_cases hcall : isCallReloc r.type = true
  · simp only [hcall, ↓reduceIte] at h
    left
    cases hl : callLink? i with
    | none => simp only [hl] at h; exact (wd_throw h).elim
    | some link =>
      simp only [hl] at h
      obtain ⟨rfl, rfl, rfl⟩ := wd_ok3 h
      exact ⟨r, y, link, rfl, hy, hcall, callLink?_eq hl, rfl, rfl, rfl⟩
  right
  simp only [hcall, Bool.false_eq_true, ↓reduceIte] at h
  unfold symPair at h
  by_cases h2 : (decide (n = 0) || decide (o + 8 > t.size)) = true
  · simp only [h2, ↓reduceIte] at h; exact (wd_throw h).elim
  simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
  have h2' : o + 8 ≤ t.size := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h2; omega
  by_cases h3 : (covering rs (o + 4) != [r]) = true
  · simp only [h3, ↓reduceIte] at h; exact (wd_throw h).elim
  simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
  have h3' : covering rs (o + 4) = [r] := by simpa using h3
  cases ha : adrpRd? i with
  | none => simp only [ha] at h; exact (wd_throw h).elim
  | some rd =>
  simp only [ha] at h
  obtain ⟨rfl, hrd⟩ := adrpRd?_eq ha
  cases hd2 : decode (wordAt t (o + 4)) with
  | none => rw [hd2] at h; unfold symPairAt at h; exact (wd_throw h).elim
  | some i2 =>
  rw [hd2] at h; unfold symPairAt at h
  refine ⟨r, y, rd, i2, rfl, hy, by simpa using hcall, h2', h3', rfl, hrd, rfl, ?_⟩
  unfold symPair2 at h
  by_cases hty : (r.type == "R_ADDRARM64") = true
  · simp only [hty, ↓reduceIte] at h
    cases hl : addLo? rd i2 with
    | none => simp only [hl] at h; exact (wd_throw h).elim
    | some rd2 =>
      simp only [hl] at h
      obtain ⟨rfl, rfl, rfl⟩ := wd_ok3 h
      exact ⟨rfl, rfl, Or.inl ⟨by simpa using hty, rd2, addLo?_eq hl, rfl⟩⟩
  simp only [hty, Bool.false_eq_true, ↓reduceIte] at h
  unfold symLdst at h
  cases hsc : ldstScale r.type with
  | none => simp only [hsc] at h; exact (wd_throw h).elim
  | some sc =>
  simp only [hsc] at h
  cases hl : ldstLo? rd sc i2 with
  | none => simp only [hl] at h; exact (wd_throw h).elim
  | some q =>
  obtain ⟨size, opc, rt⟩ := q
  simp only [hl] at h
  obtain ⟨rfl, hsz⟩ := ldstLo?_eq hl
  obtain ⟨σa, hac, h⟩ := wd_bind_ok h
  obtain ⟨rfl, rfl, rfl⟩ := wd_ok3 h
  exact ⟨rfl, rfl, Or.inr ⟨size, opc, rt, by rw [hsz], rfl, hac⟩⟩


theorem symUnit_le {n o : Nat} {σ σ' : Sym} {mc : MCtl} {used : Nat}
    (h : symUnit t rs n o σ = .ok (σ', mc, used)) : SymLe σ σ' := by
  obtain ⟨-, -, i, -, hcase⟩ := symUnit_inv h
  rcases hcase with ⟨-, -, hsi, -⟩ | ⟨r, y, link, -, -, -, -, rfl, -, -⟩ |
    ⟨r, y, rd, i2, -, -, -, -, -, -, -, -, -, -, ⟨-, rd2, -, rfl⟩ | ⟨size, opc, rt, -, -, ha⟩⟩
  · exact symInsn_le hsi
  · exact SymLe.refl _
  · exact (SymLe.of_wX σ _ _).wXsp _ _
  · exact (SymLe.of_wX σ _ _).trans (symAccess_le ha)

theorem symUnit_used {n o : Nat} {σ σ' : Sym} {mc : MCtl} {used : Nat}
    (h : symUnit t rs n o σ = .ok (σ', mc, used)) : used = 1 ∨ (used = 2 ∧ mc = .fall) := by
  obtain ⟨-, -, i, -, hcase⟩ := symUnit_inv h
  rcases hcase with ⟨-, -, -, rfl⟩ | ⟨r, y, link, -, -, -, -, -, rfl, -⟩ |
    ⟨r, y, rd, i2, -, -, -, -, -, -, -, -, rfl, rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl⟩

theorem relocAt_spec {o : Nat} {r : Reloc} (h : relocAt rs o = some r) :
    covering rs o = [r] ∧ r.off = o ∧ r.siz ≠ 0 := by
  unfold relocAt at h
  split at h
  · rename_i r' hc
    by_cases ho : (r'.off == (o : Int)) = true
    · simp only [ho, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hmem : r' ∈ covering rs o := by rw [hc]; simp
      simp only [covering, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] at hmem
      exact ⟨hc, by simpa using ho, hmem.2.1⟩
    · simp [ho] at h
  · cases h

/-- One unit (`symUnit`) runs as it says. -/
theorem symUnit_sound (hlink : linkCode base sym t rs = .ok code) (hsz : t.size ≤ 2 ^ 64)
    (hret : code retM = none) {n o : Nat} {σ σ' : Sym} {mc : MCtl} {used : Nat} {c : Ctx}
    {tm : MState} (h : symUnit t rs n o σ = .ok (σ', mc, used)) (hsym : c.sym = sym)
    (hH : Holds c σ tm) (hpc : tm.pc = base + BitVec.ofNat 64 o) (hnil : NoNil c σ') :
    ∃ tm', MStar H code retM tm tm' ∧ WordsPost c base (o + 4 * used - 4) σ' mc tm' := by
  obtain ⟨hs, ho4, i, hd, hcase⟩ := symUnit_inv h
  obtain ⟨w, hlw, hcw⟩ := linkCode_at hlink ho4 hs hsz
  rcases hcase with ⟨hr, hcov, hsi, rfl⟩ | ⟨r, y, link, hr, hy, hcall, rfl, rfl, rfl, rfl⟩ |
    ⟨r, y, rd, i2, hr, hy, hcall, hs8, hcov4, rfl, hrd, hd2, rfl, rfl, hpair⟩
  · -- a plain word
    have hw := linkWord_plain hlw hcov
    subst hw
    obtain ⟨tm', hex, hH', hx30, hctl⟩ := symInsn_sound hsi hH hpc hnil
    refine ⟨tm', mstar_single (mstep_word hcw hd hex hpc hret), hH', hx30, ?_⟩
    simpa using hctl
  · -- `BL`/`B` of `R_CALLARM64`
    obtain ⟨hcov, hoff, hsiz⟩ := relocAt_spec hr
    obtain ⟨q, hq, rfl⟩ := linkWord_one hlw hcov
    obtain ⟨imm26, hd', htgt⟩ := decode_call hd hcall hoff hy hq hsiz
    have hex : exec (.b link imm26) tm =
        .ok { (if link then tm.wX 30 (tm.pc + 4) else tm) with pc := tm.pcRel imm26 } := rfl
    refine ⟨_, mstar_single (mstep_word hcw hd' hex hpc hret), ?_⟩
    have hpcrel : tm.pcRel imm26 = sym y + BitVec.ofInt 64 r.add := by
      simp only [MState.pcRel, hpc]; exact htgt
    cases link
    · refine ⟨⟨hH.x, hH.x31, hH.sp, hH.nzcv, hH.v, hH.mem⟩, fun _ => hH.x30, ?_⟩
      simp only [CtlPc, Bool.false_eq_true, ↓reduceIte]
      rw [hpcrel, hsym]
    · refine ⟨holdsCore_wX30 hH.toHoldsCore _ _, fun hne => by simp [MCtl.links] at hne, ?_⟩
      simp only [CtlPc, ↓reduceIte]
      refine ⟨by rw [hpcrel, hsym], ?_⟩
      simp only [MState.wX, show (30 : Reg) ≠ 31 by decide, ↓reduceIte, hpc]
      exact at_close base o 4 _ (by omega)
  · -- the relocated pairs
    obtain ⟨hcov, hoff, hsiz⟩ := relocAt_spec hr
    obtain ⟨q1, hq1, rfl⟩ := linkWord_one hlw hcov
    obtain ⟨imm, hd1', hpage⟩ := decode_adrp hd hcall hoff hy hq1 hsiz
    have hex1 : exec (.adr true imm rd) tm =
        .ok ((tm.wX rd ((tm.pc &&& ~~~(0xFFF : BitVec 64)) + (imm.signExtend 64 <<< 12))).next) := rfl
    have hev : (relTgt y r).eval c = sym y + BitVec.ofInt 64 r.add := by
      simp [relTgt, Ex.eval_mkAdd, Ex.eval, hsym]
    have hrdlt : rd.toNat < 32 := rd.isLt
    have hrdofs : (BitVec.ofNat 5 rd.toNat : Reg) = rd := by simp
    have hH1 : Holds c (σ.wX rd.toNat (.page (relTgt y r)))
        ((tm.wX rd ((tm.pc &&& ~~~(0xFFF : BitVec 64)) + (imm.signExtend 64 <<< 12))).next) := by
      have h1 := hH.wX_sym hrdlt (.page (relTgt y r))
      rw [hrdofs] at h1
      have hv : (Ex.page (relTgt y r)).eval c =
          (tm.pc &&& ~~~(0xFFF : BitVec 64)) + (imm.signExtend 64 <<< 12) := by
        simp only [Ex.eval, hev, hpc]; exact hpage.symm
      rw [hv] at h1
      exact h1.pc _
    obtain ⟨tm1, htm1⟩ : ∃ tm1, tm1 =
        (tm.wX rd ((tm.pc &&& ~~~(0xFFF : BitVec 64)) + (imm.signExtend 64 <<< 12))).next :=
      ⟨_, rfl⟩
    rw [← htm1] at hH1 hex1
    have hpc1 : tm1.pc = base + BitVec.ofNat 64 (o + 4) := by
      simp only [htm1, MState.next, MState.wX]
      split <;> simp [hpc, BitVec.add_assoc, BitVec.ofNat_add]
    have hrx1 : tm1.rXsp rd = (sym y + BitVec.ofInt 64 r.add) &&& ~~~(0xFFF : BitVec 64) := by
      simp only [htm1, MState.next, MState.rXsp, MState.wX, hrd, ↓reduceIte]
      rw [hpc]; exact hpage
    obtain ⟨w2, hlw2, hcw2⟩ := linkCode_at hlink (o := o + 4) (by omega) (by omega) hsz
    obtain ⟨q2, hq2, rfl⟩ := linkWord_one hlw2 hcov4
    have hs1 : MStep H code retM tm tm1 := mstep_word hcw hd1' hex1 hpc hret
    rcases hpair with ⟨hty, rd2, rfl, rfl⟩ | ⟨size, opc, rt, hsc, rfl, ha⟩
    · obtain ⟨imm12, hd2', hlo⟩ := decode_addLo hd2 hty hoff hy hq2 hsiz
      have hex2 : exec (.addSubImm true false false false imm12 rd rd2) tm1 =
          .ok ((tm1.wXsp rd2 (sym y + BitVec.ofInt 64 r.add)).next) := by
        have hadd : (addSub true false (tm1.rXsp rd) (imm12.setWidth 64 <<< 0)).1 =
            sym y + BitVec.ofInt 64 r.add := by
          rw [hrx1]
          have : ∀ x z : BitVec 64, (addSub true false x z).1 = x + z := by
            intro x z; apply BitVec.eq_of_toNat_eq
            simp [addSub, sizedF, GoFV.SSA.Sem.addWithCarry, BitVec.toNat_add]
          rw [this]; simpa using hlo
        simp only [exec, MState.addSubResult, Bool.false_eq_true, ↓reduceIte, hadd]
        rfl
      have hrd2 : (BitVec.ofNat 5 rd2.toNat : Reg) = rd2 := by simp
      have hH2 := hH1.wXsp_sym rd2.isLt (relTgt y r)
      rw [hrd2, hev] at hH2
      refine ⟨_, mstar_trans (mstar_single hs1) (mstar_single (mstep_word hcw2 hd2' hex2 hpc1 hret)),
        (hH2.pc _).toHoldsCore, fun _ => (hH2.pc _).x30, ?_⟩
      simp only [CtlPc, MState.next, MState.wXsp]
      split <;> (show tm1.pc + 4 = _; rw [hpc1]; exact at_close base (o + 4) 4 _ (by omega))
    · obtain ⟨imm12, hd2', hlo⟩ := decode_ldstLo hd2 hsc hoff hy hq2 hsiz
      have haddr : (tm1.amode (.uimm imm12) rd (bytesOf size)).1 = (relTgt y r).eval c := by
        simp only [MState.amode, hrx1, hev, bytesOf]; exact hlo
      obtain ⟨tm2, hex2, hH2, hpc2⟩ := symAccess_exec ha hH1 rt.isLt haddr rfl hnil
      have hrt : (BitVec.ofNat 5 rt.toNat : Reg) = rt := by simp
      rw [hrt] at hex2
      have hex2' : exec (.ldst size false opc (.uimm imm12) rd rt) tm1 = .ok tm2 := hex2
      refine ⟨tm2, mstar_trans (mstar_single hs1) (mstar_single (mstep_word hcw2 hd2' hex2' hpc1 hret)),
        hH2.toHoldsCore, fun _ => hH2.x30, ?_⟩
      rw [CtlPc, hpc2, hpc1]
      exact at_close base (o + 4) 4 _ (by omega)

/-- `symWords` only adds loads and stores. -/
theorem symWords_le : ∀ (n o : Nat) (σ σ' : Sym) (mc : MCtl),
    symWords t rs (n + 1) o σ = .ok (σ', mc) → SymLe σ σ' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro o σ σ' mc h
  simp only [symWords, bind, Except.bind] at h
  cases hu : symUnit t rs n o σ with
  | error e => rw [hu] at h; cases h
  | ok r =>
  obtain ⟨σ1, c1, used⟩ := r
  rw [hu] at h
  simp only at h
  have hle1 := symUnit_le hu
  rcases symUnit_used hu with rfl | ⟨rfl, rfl⟩
  · simp only [show (1 = 2) = False by decide, ↓reduceIte] at h
    by_cases hn : n = 0
    · subst hn
      simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hle1
    · simp only [hn, ↓reduceIte] at h
      split at h
      · cases h
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        exact hle1.trans (ih n' (by omega) _ _ _ _ h)
  · simp only [↓reduceIte] at h
    match n, h with
    | 0, h => cases h
    | m + 1, h =>
      simp only at h
      by_cases hm : m = 0
      · subst hm
        simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hle1
      · simp only [hm, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true] at h
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        exact hle1.trans (ih m' (by omega) _ _ _ _ h)

/-- The words accepted by `symWords` run as it says. -/
theorem symWords_sound (hlink : linkCode base sym t rs = .ok code) (hsz : t.size ≤ 2 ^ 64)
    (hret : code retM = none) :
    ∀ (n o : Nat) (σ σ' : Sym) (mc : MCtl) (c : Ctx) (tm : MState),
      symWords t rs (n + 1) o σ = .ok (σ', mc) → c.sym = sym → Holds c σ tm →
      tm.pc = base + BitVec.ofNat 64 o → NoNil c σ' →
      ∃ tm', MStar H code retM tm tm' ∧ WordsPost c base (o + 4 * n) σ' mc tm' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro o σ σ' mc c tm h hsym hH hpc hnil
  have hall := h
  simp only [symWords, bind, Except.bind] at h
  cases hu : symUnit t rs n o σ with
  | error e => rw [hu] at h; cases h
  | ok r =>
  obtain ⟨σ1, c1, used⟩ := r
  rw [hu] at h
  simp only at h
  rcases symUnit_used hu with rfl | ⟨rfl, rfl⟩
  · -- one word
    simp only [show (1 = 2) = False by decide, ↓reduceIte] at h
    by_cases hn : n = 0
    · subst hn
      simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨tm1, hs1, hp1⟩ := symUnit_sound hlink hsz hret hu hsym hH hpc hnil
      exact ⟨tm1, hs1, by simpa using hp1⟩
    · simp only [hn, ↓reduceIte] at h
      split at h
      · cases h
      · rename_i hc1
        have hc1 : c1 = .fall := by simpa using hc1
        subst hc1
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        have hle2 := symWords_le n' (o + 4) σ1 σ' mc h
        obtain ⟨tm1, hs1, hc1, hx1, hp1⟩ :=
          symUnit_sound hlink hsz hret hu hsym hH hpc (hnil.mono hle2)
        have hH1 : Holds c σ1 tm1 := ⟨hc1, hx1 rfl⟩
        have hpc1 : tm1.pc = base + BitVec.ofNat 64 (o + 4) := by
          simp only [CtlPc] at hp1; rw [hp1, at_nat]; congr 1
        obtain ⟨tm2, hs2, hp2⟩ := ih n' (by omega) (o + 4) σ1 σ' mc c tm1 h hsym hH1 hpc1 hnil
        exact ⟨tm2, mstar_trans hs1 hs2, by
          have : o + 4 + 4 * n' = o + 4 * (n' + 1) := by omega
          simpa [this] using hp2⟩
  · -- a relocated pair
    simp only [↓reduceIte] at h
    match n, h with
    | 0, h => cases h
    | m + 1, h =>
      simp only at h
      by_cases hm : m = 0
      · subst hm
        simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨tm1, hs1, hp1⟩ := symUnit_sound hlink hsz hret hu hsym hH hpc hnil
        exact ⟨tm1, hs1, by simpa using hp1⟩
      · simp only [hm, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true] at h
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have hle2 := symWords_le m' (o + 8) σ1 σ' mc h
        obtain ⟨tm1, hs1, hc1, hx1, hp1⟩ :=
          symUnit_sound hlink hsz hret hu hsym hH hpc (hnil.mono hle2)
        have hH1 : Holds c σ1 tm1 := ⟨hc1, hx1 rfl⟩
        have hpc1 : tm1.pc = base + BitVec.ofNat 64 (o + 8) := by
          simp only [CtlPc] at hp1; rw [hp1, at_nat]; congr 1
        obtain ⟨tm2, hs2, hp2⟩ := ih m' (by omega) (o + 8) σ1 σ' mc c tm1 h hsym hH1 hpc1 hnil
        exact ⟨tm2, mstar_trans hs1 hs2, by
          have : o + 8 + 4 * m' = o + 4 * (m' + 1 + 1) := by omega
          simpa [this] using hp2⟩

/-! ## Faults: a word whose access is in the nil page -/

/-- The machine is at a word that faults in the nil page. -/
def WordFault (code : Code) (retM : BitVec 64) (tm : MState) : Prop :=
  tm.pc ≠ retM ∧ code tm.pc ≠ none ∧ ∃ a, step code tm = .error (.nilPage a)

private theorem wordFault_of {tm : MState} {w : BitVec 32} {i : Insn} {x : BitVec 64}
    (hret : code retM = none) (hc : code tm.pc = some w) (hd : decode w = some i)
    (he : exec i tm = .error (.nilPage x)) : WordFault code retM tm := by
  unfold WordFault
  refine ⟨fun h => ?_, by rw [hc]; simp, x, by simp [step, hc, hd, he]⟩
  rw [h, hret] at hc
  cases hc

/-- One unit (`symUnit`) whose effect adds an access in the nil page (none before it): the
machine runs to a word that faults. -/
theorem symUnit_fault (hlink : linkCode base sym t rs = .ok code) (hsz : t.size ≤ 2 ^ 64)
    (hret : code retM = none) {n o : Nat} {σ σ' : Sym} {mc : MCtl} {used : Nat} {c : Ctx}
    {tm : MState} (h : symUnit t rs n o σ = .ok (σ', mc, used)) (hsym : c.sym = sym)
    (hH : Holds c σ tm) (hpc : tm.pc = base + BitVec.ofNat 64 o) (hN : NoNil c σ)
    (hbad : ¬ NoNil c σ') : ∃ tm', MStar H code retM tm tm' ∧ WordFault code retM tm' := by
  obtain ⟨hs, ho4, i, hd, hcase⟩ := symUnit_inv h
  obtain ⟨w, hlw, hcw⟩ := linkCode_at hlink ho4 hs hsz
  rcases hcase with ⟨hr, hcov, hsi, rfl⟩ | ⟨r, y, link, hr, hy, hcall, rfl, rfl, rfl, rfl⟩ |
    ⟨r, y, rd, i2, hr, hy, hcall, hs8, hcov4, rfl, hrd, hd2, rfl, rfl, hpair⟩
  · have hw := linkWord_plain hlw hcov
    subst hw
    obtain ⟨x, hx⟩ := symInsn_fault hsi hH hN hbad
    rw [← hpc] at hcw
    exact ⟨tm, .refl, wordFault_of hret hcw hd hx⟩
  · exact absurd hN hbad
  · rcases hpair with ⟨hty, rd2, rfl, rfl⟩ | ⟨size, opc, rt, hsc, rfl, ha⟩
    · exact absurd (NoNil.of_same (by simp) (by simp) hN) hbad
    obtain ⟨hcov, hoff, hsiz⟩ := relocAt_spec hr
    obtain ⟨q1, hq1, rfl⟩ := linkWord_one hlw hcov
    obtain ⟨imm, hd1', hpage⟩ := decode_adrp hd hcall hoff hy hq1 hsiz
    have hex1 : exec (.adr true imm rd) tm =
        .ok ((tm.wX rd ((tm.pc &&& ~~~(0xFFF : BitVec 64)) + (imm.signExtend 64 <<< 12))).next) := rfl
    have hev : (relTgt y r).eval c = sym y + BitVec.ofInt 64 r.add := by
      simp [relTgt, Ex.eval_mkAdd, Ex.eval, hsym]
    have hrdofs : (BitVec.ofNat 5 rd.toNat : Reg) = rd := by simp
    have hH1 : Holds c (σ.wX rd.toNat (.page (relTgt y r)))
        ((tm.wX rd ((tm.pc &&& ~~~(0xFFF : BitVec 64)) + (imm.signExtend 64 <<< 12))).next) := by
      have h1 := hH.wX_sym rd.isLt (.page (relTgt y r))
      rw [hrdofs] at h1
      have hv : (Ex.page (relTgt y r)).eval c =
          (tm.pc &&& ~~~(0xFFF : BitVec 64)) + (imm.signExtend 64 <<< 12) := by
        simp only [Ex.eval, hev, hpc]; exact hpage.symm
      rw [hv] at h1
      exact h1.pc _
    obtain ⟨tm1, htm1⟩ : ∃ tm1, tm1 =
        (tm.wX rd ((tm.pc &&& ~~~(0xFFF : BitVec 64)) + (imm.signExtend 64 <<< 12))).next :=
      ⟨_, rfl⟩
    rw [← htm1] at hH1 hex1
    have hpc1 : tm1.pc = base + BitVec.ofNat 64 (o + 4) := by
      simp only [htm1, MState.next, MState.wX]
      split <;> simp [hpc, BitVec.add_assoc, BitVec.ofNat_add]
    have hrx1 : tm1.rXsp rd = (sym y + BitVec.ofInt 64 r.add) &&& ~~~(0xFFF : BitVec 64) := by
      simp only [htm1, MState.next, MState.rXsp, MState.wX, hrd, ↓reduceIte]
      rw [hpc]; exact hpage
    obtain ⟨w2, hlw2, hcw2⟩ := linkCode_at hlink (o := o + 4) (by omega) (by omega) hsz
    obtain ⟨q2, hq2, rfl⟩ := linkWord_one hlw2 hcov4
    have hs1 : MStep H code retM tm tm1 := mstep_word hcw hd1' hex1 hpc hret
    obtain ⟨imm12, hd2', hlo⟩ := decode_ldstLo hd2 hsc hoff hy hq2 hsiz
    have haddr : (tm1.amode (.uimm imm12) rd (bytesOf size)).1 = (relTgt y r).eval c := by
      simp only [MState.amode, hrx1, hev, bytesOf]; exact hlo
    have hN1 : NoNil c (σ.wX rd.toNat (.page (relTgt y r))) :=
      NoNil.of_same (by simp) (by simp) hN
    obtain ⟨x, hx⟩ := symAccess_fault ha (Prod.ext haddr rfl) hN1 hbad
    have hrt : (BitVec.ofNat 5 rt.toNat : Reg) = rt := by simp
    rw [hrt] at hx
    rw [← hpc1] at hcw2
    exact ⟨tm1, mstar_single hs1, wordFault_of hret hcw2 hd2' hx⟩

/-- Words accepted by `symWords` whose effect has an access in the nil page (from a state
without one): the machine runs to a word that faults. -/
theorem symWords_fault (hlink : linkCode base sym t rs = .ok code) (hsz : t.size ≤ 2 ^ 64)
    (hret : code retM = none) :
    ∀ (n o : Nat) (σ σ' : Sym) (mc : MCtl) (c : Ctx) (tm : MState),
      symWords t rs (n + 1) o σ = .ok (σ', mc) → c.sym = sym → Holds c σ tm →
      tm.pc = base + BitVec.ofNat 64 o → NoNil c σ → ¬ NoNil c σ' →
      ∃ tm', MStar H code retM tm tm' ∧ WordFault code retM tm' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro o σ σ' mc c tm h hsym hH hpc hN hbad
  simp only [symWords, bind, Except.bind] at h
  cases hu : symUnit t rs n o σ with
  | error e => rw [hu] at h; cases h
  | ok r =>
  obtain ⟨σ1, c1, used⟩ := r
  rw [hu] at h
  simp only at h
  by_cases hN1 : NoNil c σ1
  case neg => exact symUnit_fault hlink hsz hret hu hsym hH hpc hN hN1
  rcases symUnit_used hu with rfl | ⟨rfl, rfl⟩
  · simp only [show (1 = 2) = False by decide, ↓reduceIte] at h
    by_cases hn : n = 0
    · subst hn
      simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact absurd hN1 hbad
    · simp only [hn, ↓reduceIte] at h
      split at h
      · cases h
      · rename_i hc1
        have hc1 : c1 = .fall := by simpa using hc1
        subst hc1
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        obtain ⟨tm1, hs1, hc1, hx1, hp1⟩ := symUnit_sound hlink hsz hret hu hsym hH hpc hN1
        have hH1 : Holds c σ1 tm1 := ⟨hc1, hx1 rfl⟩
        have hpc1 : tm1.pc = base + BitVec.ofNat 64 (o + 4) := by
          simp only [CtlPc] at hp1; rw [hp1, at_nat]; congr 1
        obtain ⟨tm2, hs2, hf⟩ := ih n' (by omega) (o + 4) σ1 σ' mc c tm1 h hsym hH1 hpc1 hN1 hbad
        exact ⟨tm2, mstar_trans hs1 hs2, hf⟩
  · simp only [↓reduceIte] at h
    match n, h with
    | 0, h => cases h
    | m + 1, h =>
      simp only at h
      by_cases hm : m = 0
      · subst hm
        simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact absurd hN1 hbad
      · simp only [hm, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true] at h
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        obtain ⟨tm1, hs1, hc1, hx1, hp1⟩ := symUnit_sound hlink hsz hret hu hsym hH hpc hN1
        have hH1 : Holds c σ1 tm1 := ⟨hc1, hx1 rfl⟩
        have hpc1 : tm1.pc = base + BitVec.ofNat 64 (o + 8) := by
          simp only [CtlPc] at hp1; rw [hp1, at_nat]; congr 1
        obtain ⟨tm2, hs2, hf⟩ := ih m' (by omega) (o + 8) σ1 σ' mc c tm1 h hsym hH1 hpc1 hN1 hbad
        exact ⟨tm2, mstar_trans hs1 hs2, hf⟩

end GoFV.Proof.Obj
