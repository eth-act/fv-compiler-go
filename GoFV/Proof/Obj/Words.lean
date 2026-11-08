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

/-- What the state after words with effect `σ` and control `mc`, the last at `ol`, satisfies. -/
def WordsPost (c : Ctx) (base : BitVec 64) (ol : Nat) (σ : Sym) (mc : MCtl) (tm : MState) : Prop :=
  HoldsCore c σ tm ∧ (∀ y a, mc ≠ .call y a → tm.x 30 = (σ.getX 30).eval c) ∧
    CtlPc c base ol mc tm

theorem at_succ (base : BitVec 64) (o k : Nat) :
    base + BitVec.ofNat 64 o + BitVec.ofNat 64 k = at_ base ((o + k : Nat) : Int) := by
  simp only [at_, BitVec.ofInt_natCast, BitVec.add_assoc, BitVec.ofNat_add]

theorem at_nat (base : BitVec 64) (o : Nat) : base + BitVec.ofNat 64 o = at_ base (o : Int) := by
  simp [at_]

/-- The target of a relocation, as `symUnit` writes it. -/
def relTgt (y : Nat) (r : Reloc) : Ex := Ex.mkAdd (.sym y) (.k (BitVec.ofInt 64 r.add))

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
  by_cases h1 : (o + 4 > t.size || o % 4 != 0) = true
  · simp [h1] at h
  have h1' : o + 4 ≤ t.size ∧ o % 4 = 0 := by simp at h1; omega
  simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
  refine ⟨h1'.1, h1'.2, ?_⟩
  cases hd : decode (wordAt t o) with
  | none => simp [hd] at h
  | some i =>
  simp only [hd] at h
  refine ⟨i, rfl, ?_⟩
  cases hr : relocAt rs o with
  | none =>
    simp only [hr] at h
    by_cases hc : (!(covering rs o).isEmpty) = true
    · simp [hc] at h
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      cases hs : symInsn i o σ with
      | error e => simp [hs, bind, Except.bind] at h
      | ok q =>
        simp [hs, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        left
        exact ⟨rfl, by simpa using hc, rfl, rfl⟩
  | some r =>
    simp only [hr] at h
    cases hy : r.sym with
    | none => simp [hy] at h
    | some y =>
    simp only [hy] at h
    right
    by_cases hcall : isCallReloc r.type = true
    · simp only [hcall, ↓reduceIte] at h
      left
      cases hl : callLink? i with
      | none => simp [hl] at h
      | some link =>
        simp [hl, pure, Except.pure] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨r, y, link, rfl, hy, hcall, callLink?_eq hl, rfl, rfl, rfl⟩
    · right
      simp only [hcall, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h2 : (n = 0 || o + 8 > t.size) = true
      · simp [h2] at h
      simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
      have h2' : o + 8 ≤ t.size := by simp at h2; omega
      by_cases h3 : (covering rs (o + 4) != [r]) = true
      · simp [h3] at h
      simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
      have h3' : covering rs (o + 4) = [r] := by simpa using h3
      cases ha : adrpRd? i with
      | none => simp [ha] at h
      | some rd =>
      simp only [ha] at h
      obtain ⟨rfl, hrd⟩ := adrpRd?_eq ha
      cases hd2 : decode (wordAt t (o + 4)) with
      | none => simp [hd2] at h
      | some i2 =>
      simp only [hd2] at h
      refine ⟨r, y, rd, i2, rfl, hy, by simpa using hcall, h2', h3', rfl, hrd, rfl, ?_⟩
      by_cases hty : (r.type == "R_ADDRARM64") = true
      · simp only [hty, ↓reduceIte] at h
        cases hl : addLo? rd i2 with
        | none => simp [hl] at h
        | some rd2 =>
          simp [hl, pure, Except.pure] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨rfl, rfl, Or.inl ⟨by simpa using hty, rd2, addLo?_eq hl, rfl⟩⟩
      · simp only [hty, Bool.false_eq_true, ↓reduceIte] at h
        cases hsc : ldstScale r.type with
        | none => simp [hsc] at h
        | some sc =>
        simp only [hsc] at h
        cases hl : ldstLo? rd sc i2 with
        | none => simp [hl] at h
        | some q =>
        obtain ⟨size, opc, rt⟩ := q
        simp only [hl] at h
        obtain ⟨rfl, hsz⟩ := ldstLo?_eq hl
        cases hac : symAccess (σ.wX rd.toNat (.page (relTgt y r))) size opc rt.toNat (relTgt y r) with
        | error e => simp [relTgt] at hac; simp [hac, bind, Except.bind] at h
        | ok σa =>
          simp [relTgt] at hac
          simp [hac, bind, Except.bind, pure, Except.pure] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨rfl, rfl, Or.inr ⟨size, opc, rt, by rw [hsz], rfl, by simpa [relTgt] using hac⟩⟩

theorem symUnit_le {n o : Nat} {σ σ' : Sym} {mc : MCtl} {used : Nat}
    (h : symUnit t rs n o σ = .ok (σ', mc, used)) : SymLe σ σ' := by
  obtain ⟨-, -, i, -, hcase⟩ := symUnit_inv h
  rcases hcase with ⟨-, -, hsi, -⟩ | ⟨r, y, link, -, -, -, -, rfl, -, -⟩ |
    ⟨r, y, rd, i2, -, -, -, -, -, -, -, -, -, -, ⟨-, rd2, -, rfl⟩ | ⟨size, opc, rt, -, -, ha⟩⟩
  · exact symInsn_le hsi
  · exact SymLe.refl σ
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

theorem holdsCore_wX30 {c : Ctx} {σ : Sym} {tm : MState} (h : HoldsCore c σ tm) (v q : BitVec 64) :
    HoldsCore c σ { tm.wX 30 v with pc := q } := by
  obtain ⟨hx, h31, hsp, hfl, hv, hmem⟩ := h
  refine ⟨fun r hr => ?_, ?_, hsp, hfl, hv, hmem⟩
  · have : (BitVec.ofNat 5 r : Reg) ≠ 30 := by
      intro he; have := congrArg BitVec.toNat he; simp at this; omega
    simp [MState.wX, this, hx r hr]
  · simp [MState.wX, h31]

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
    obtain ⟨tm', hex, hH', hctl⟩ := symInsn_sound hsi hH hpc hnil
    refine ⟨tm', mstar_single (mstep_word hcw hd hex hpc hret), hH'.toHoldsCore,
      fun _ _ _ => hH'.x30, ?_⟩
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
    · refine ⟨⟨hH.x, hH.x31, hH.sp, hH.nzcv, hH.v, hH.mem⟩, fun _ _ _ => hH.x30, ?_⟩
      simp only [CtlPc, Bool.false_eq_true, ↓reduceIte]
      rw [hpcrel, hsym]
    · refine ⟨holdsCore_wX30 hH.toHoldsCore _ _, fun y' a' hne => absurd rfl hne, ?_⟩
      simp only [CtlPc, ↓reduceIte]
      refine ⟨by rw [hpcrel, hsym], ?_⟩
      simp only [MState.wX, show (30 : Reg) ≠ 31 by decide, ↓reduceIte, hpc, at_succ]
      simp
  · -- the relocated pairs
    sorry



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
        have hH1 : Holds c σ1 tm1 := ⟨hc1, hx1 0 0 (by simp)⟩
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
        have hH1 : Holds c σ1 tm1 := ⟨hc1, hx1 0 0 (by simp)⟩
        have hpc1 : tm1.pc = base + BitVec.ofNat 64 (o + 8) := by
          simp only [CtlPc] at hp1; rw [hp1, at_nat]; congr 1
        obtain ⟨tm2, hs2, hp2⟩ := ih m' (by omega) (o + 8) σ1 σ' mc c tm1 h hsym hH1 hpc1 hnil
        exact ⟨tm2, mstar_trans hs1 hs2, by
          have : o + 8 + 4 * m' = o + 4 * (m' + 1 + 1) := by omega
          simpa [this] using hp2⟩

end GoFV.Proof.Obj
