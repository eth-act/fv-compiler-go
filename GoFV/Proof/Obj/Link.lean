import GoFV.Proof.Obj.Basic

/-!
# The linked words (`GoFV/Asm/CheckObjLink.lean`)

`linkCode` places a word of the text at `base + o`; a word no relocation patches is the text's
word; a relocated word decodes to the instruction the validator read with the relocated field
filled in so that it reaches the target `sym y + add`: `BL`/`B` (`R_CALLARM64`), `ADRP`
(`R_ADDRARM64`, `R_ARM64_PCREL_LDST*`: the target's page), and the `ADD` or load/store after it
(the target's offset in its page).
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj

variable {base : BitVec 64} {sym : Nat → BitVec 64} {t : ByteArray} {rs : List Reloc}
  {code : Code}

/-! ### `Except` plumbing -/

private theorem lnk_bind_ok {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {b : β}
    (h : (x >>= g) = .ok b) : ∃ a, x = .ok a ∧ g a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem lnk_forIn_ok {f : Nat → Except String (BitVec 32)} :
    ∀ (l : List Nat) {u : PUnit},
      forIn l PUnit.unit (fun o _ => do let _ ← f o; pure (ForInStep.yield PUnit.unit)) =
        (.ok u : Except String PUnit) → ∀ x ∈ l, ∃ v, f x = .ok v
  | [], _, _, x, hx => by simp at hx
  | a :: l, u, h, x, hx => by
    rw [List.forIn_cons] at h
    obtain ⟨s, h1, h2⟩ := lnk_bind_ok h
    obtain ⟨v, hv, h3⟩ := lnk_bind_ok h1
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨v, hv⟩
    · have hs : s = .yield PUnit.unit := (Except.ok.inj h3).symm
      subst hs
      exact lnk_forIn_ok l h2 x hx

/-- The word at a text offset is mapped at `base + o`. -/
theorem linkCode_at (h : linkCode base sym t rs = .ok code) {o : Nat} (ho : o % 4 = 0)
    (hs : o + 4 ≤ t.size) (hsz : t.size ≤ 2 ^ 64) :
    ∃ w, linkWord base sym t rs o = .ok w ∧ code (base + BitVec.ofNat 64 o) = some w := by
  unfold linkCode at h
  obtain ⟨u, hfor, hret⟩ := lnk_bind_ok h
  have hcode := Except.ok.inj hret
  obtain ⟨v, hv⟩ := lnk_forIn_ok (f := fun o => linkWord base sym t rs (4 * o)) _ hfor (o / 4)
    (List.mem_range.2 (by omega))
  have h4 : 4 * (o / 4) = o := by omega
  simp only [h4] at hv
  refine ⟨v, hv, ?_⟩
  rw [← hcode]
  have hd : (base + BitVec.ofNat 64 o - base).toNat = o := by
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := base.isLt
    omega
  simp only [hd, ho, hs, and_self, ↓reduceIte, hv, Except.toOption]

/-! ### `linkWord` -/

private theorem lnk_or_zero {n : Nat} {x : BitVec n} : x ||| 0 = x := BitVec.or_zero

private theorem lnk_zero_or {n : Nat} {x : BitVec n} : 0 ||| x = x := BitVec.zero_or

private theorem lnk_patch_zero {r : Reloc} {o : Nat} {q : BitVec 32}
    (h : relocPatch base sym r o = .ok q)
    (hc : (r.siz != 0 && (r.off == (o : Int) || (!isCallReloc r.type && r.off + 4 == (o : Int))))
      = false) : q = 0 := by
  unfold relocPatch at h
  by_cases hs : r.siz = 0
  · have h0 : (r.siz == 0) = true := by simpa using hs
    simp only [h0, ↓reduceIte] at h
    exact (Except.ok.inj h).symm
  · have h0 : (r.siz == 0) = false := by simpa using hs
    have hs' : (r.siz != 0) = true := by simpa using hs
    simp only [hs', Bool.true_and, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      Bool.and_eq_false_iff, Bool.not_eq_false'] at hc
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · by_cases hk : isCallReloc r.type = true
      · have h1 : (r.off != (o : Int)) = true := by simpa using hc.1
        simp only [hk, h1, ↓reduceIte] at h
        exact (Except.ok.inj h).symm
      · have hk' : ¬ (r.off + 4 = (o : Int)) := by
          rcases hc.2 with hc2 | hc2
          · exact absurd hc2 hk
          · exact hc2
        have h1 : (r.off != (o : Int) && r.off + 4 != (o : Int)) = true := by
          simpa using ⟨hc.1, hk'⟩
        simp only [hk, Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · simp only [h1, ↓reduceIte] at h
          exact (Except.ok.inj h).symm
        · cases h
    · cases h

private theorem lnk_covering_cons {r : Reloc} {rs : List Reloc} {o : Nat} :
    covering (r :: rs) o =
      if (r.siz != 0 && (r.off == (o : Int) || (!isCallReloc r.type && r.off + 4 == (o : Int))))
        = true then r :: covering rs o else covering rs o := by
  unfold covering
  rw [List.filter_cons]

private theorem lnk_fold {o : Nat} : ∀ (rs : List Reloc) (w0 w : BitVec 32),
    rs.foldlM (fun w r => do return w ||| (← relocPatch base sym r o)) w0 = .ok w →
    (covering rs o = [] → w = w0) ∧
      (∀ r, covering rs o = [r] → ∃ q, relocPatch base sym r o = .ok q ∧ w = w0 ||| q)
  | [], w0, w, h => by
    have hw : w0 = w := Except.ok.inj h
    subst hw
    exact ⟨fun _ => rfl, fun r hc => by simp [covering] at hc⟩
  | r :: rs, w0, w, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨w1, h1, h2⟩ := lnk_bind_ok h
    obtain ⟨q, hq, hw1⟩ := lnk_bind_ok h1
    have hw1' : w1 = w0 ||| q := (Except.ok.inj hw1).symm
    have ih := lnk_fold rs w1 w h2
    rw [lnk_covering_cons]
    by_cases hp : (r.siz != 0 && (r.off == (o : Int) ||
        (!isCallReloc r.type && r.off + 4 == (o : Int)))) = true
    · simp only [hp, ↓reduceIte]
      refine ⟨fun hc => absurd hc (List.cons_ne_nil _ _), fun r' hc => ?_⟩
      simp only [List.cons.injEq] at hc
      obtain ⟨rfl, hc⟩ := hc
      exact ⟨q, hq, by rw [ih.1 hc, hw1']⟩
    · have hq0 : q = 0 := lnk_patch_zero hq (by simpa using hp)
      simp only [hp, Bool.false_eq_true, ↓reduceIte]
      rw [hw1', hq0, lnk_or_zero] at ih
      exact ih

/-- A word no relocation patches is the text's word. -/
theorem linkWord_plain {o : Nat} {w : BitVec 32} (h : linkWord base sym t rs o = .ok w)
    (hc : covering rs o = []) : w = wordAt t o :=
  (lnk_fold rs (wordAt t o) w h).1 hc

/-- A word one relocation patches is the text's word ORed with that relocation's patch. -/
theorem linkWord_one {o : Nat} {w : BitVec 32} {r : Reloc} (h : linkWord base sym t rs o = .ok w)
    (hc : covering rs o = [r]) : ∃ q, relocPatch base sym r o = .ok q ∧ w = wordAt t o ||| q :=
  (lnk_fold rs (wordAt t o) w h).2 r hc

/-! ### The patches `relocPatch` computes -/

private theorem lnk_patch_call {r : Reloc} {o y : Nat} {q : BitVec 32} (hsiz : r.siz ≠ 0)
    (hy : r.sym = some y) (hcall : isCallReloc r.type = true) (hoff : r.off = o)
    (hp : relocPatch base sym r o = .ok q) :
    -134217728 ≤ (sym y + BitVec.ofInt 64 r.add - (base + BitVec.ofNat 64 o)).toInt ∧
    (sym y + BitVec.ofInt 64 r.add - (base + BitVec.ofNat 64 o)).toInt < 134217728 ∧
    (sym y + BitVec.ofInt 64 r.add - (base + BitVec.ofNat 64 o)).toInt % 4 = 0 ∧
    q = BitVec.ofInt 32 ((sym y + BitVec.ofInt 64 r.add - (base + BitVec.ofNat 64 o)).toInt / 4)
      &&& 0x3ffffff := by
  unfold relocPatch at hp
  have h0 : (r.siz == 0) = false := by simpa using hsiz
  have h1 : (r.off != (o : Int)) = false := by simp [hoff]
  simp only [h0, hy, hcall, h1, Bool.false_eq_true, ↓reduceIte] at hp
  generalize (sym y + BitVec.ofInt 64 r.add - (base + BitVec.ofNat 64 o)).toInt = d at hp ⊢
  split at hp
  · cases hp
  · rename_i hc
    simp at hc
    refine ⟨by omega, by omega, by omega, (Except.ok.inj hp).symm⟩

private theorem lnk_patch_hi {r : Reloc} {o y : Nat} {q : BitVec 32} (hsiz : r.siz ≠ 0)
    (hy : r.sym = some y) (hcall : isCallReloc r.type = false) (hoff : r.off = o)
    (hp : relocPatch base sym r o = .ok q) :
    -4294967296 ≤ (sym y + BitVec.ofInt 64 r.add -
        ((base + BitVec.ofNat 64 o) &&& ~~~(0xFFF : BitVec 64))).toInt ∧
    (sym y + BitVec.ofInt 64 r.add -
        ((base + BitVec.ofNat 64 o) &&& ~~~(0xFFF : BitVec 64))).toInt < 4294967296 ∧
    ∃ A B : Nat, A < 4 ∧ B < 524288 ∧ q = BitVec.ofNat 32 (A * 536870912 + B * 32) ∧
      (A : Int) = (sym y + BitVec.ofInt 64 r.add -
        ((base + BitVec.ofNat 64 o) &&& ~~~(0xFFF : BitVec 64))).toInt / 4096 % 4 ∧
      (B : Int) = (sym y + BitVec.ofInt 64 r.add -
        ((base + BitVec.ofNat 64 o) &&& ~~~(0xFFF : BitVec 64))).toInt / 16384 % 524288 := by
  unfold relocPatch at hp
  have h0 : (r.siz == 0) = false := by simpa using hsiz
  have h2 : (r.off != (o : Int) && r.off + 4 != (o : Int)) = false := by simp [hoff]
  have h3 : (r.off == (o : Int)) = true := by simp [hoff]
  have h4 : ¬ r.off < 0 := by omega
  have h5 : BitVec.ofInt 64 r.off = BitVec.ofNat 64 o := by rw [hoff]; rfl
  simp only [h0, hy, hcall, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte] at hp
  generalize (sym y + BitVec.ofInt 64 r.add -
    ((base + BitVec.ofNat 64 o) &&& ~~~(0xFFF : BitVec 64))).toInt = tt at hp ⊢
  split at hp
  · split at hp
    · cases hp
    · rename_i hc
      simp at hc
      exact ⟨by omega, by omega, (tt / 4096 % 4).toNat, (tt / 16384 % 524288).toNat, by omega,
        by omega, (Except.ok.inj hp).symm, by omega, by omega⟩
  · cases hp

private theorem lnk_patch_lo {r : Reloc} {o y sc : Nat} {q : BitVec 32} (hsiz : r.siz ≠ 0)
    (hy : r.sym = some y) (hcall : isCallReloc r.type = false)
    (hsc : (if r.type == "R_ADDRARM64" then some 0 else ldstScale r.type) = some sc)
    (hoff : r.off = o) (hp : relocPatch base sym r (o + 4) = .ok q) :
    ∃ k, k * 2 ^ sc = (sym y + BitVec.ofInt 64 r.add).toNat % 4096 ∧ k < 4096 ∧
      q = BitVec.ofNat 32 (k * 1024) := by
  unfold relocPatch at hp
  have h0 : (r.siz == 0) = false := by simpa using hsiz
  have h2 : (r.off != ((o + 4 : Nat) : Int) && r.off + 4 != ((o + 4 : Nat) : Int)) = false := by
    rw [hoff]; simp
  have h3 : (r.off == ((o + 4 : Nat) : Int)) = false := by rw [hoff]; simp <;> omega
  have h4 : ¬ r.off < 0 := by omega
  simp only [h0, hy, hcall, hsc, h2, h3, h4, Bool.false_eq_true, ↓reduceIte] at hp
  have hlo : (sym y + BitVec.ofInt 64 r.add).toNat % 4096 < 4096 := Nat.mod_lt _ (by decide)
  generalize (sym y + BitVec.ofInt 64 r.add).toNat % 4096 = lo at hp hlo ⊢
  split at hp
  · cases hp
  · split at hp
    · cases hp
    · rename_i hc
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hc
      exact ⟨lo / 2 ^ sc, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hc),
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlo, (Except.ok.inj hp).symm⟩

/-! ### Bits -/

private theorem lnk_forall_lt_4 {p : Nat → Prop} : (∀ i, i < 4 → p i) ↔ p 0 ∧ p 1 ∧ p 2 ∧ p 3 := by
  constructor
  · intro h; exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩
  · rintro ⟨h0, h1, h2, h3⟩ i hi
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | _ + 4, h => exact absurd h (by omega)

private theorem lnk_forall_lt_32 {p : Nat → Prop} : (∀ i, i < 32 → p i) ↔
    p 0 ∧ p 1 ∧ p 2 ∧ p 3 ∧ p 4 ∧ p 5 ∧ p 6 ∧ p 7 ∧ p 8 ∧ p 9 ∧ p 10 ∧ p 11 ∧ p 12 ∧ p 13 ∧
    p 14 ∧ p 15 ∧ p 16 ∧ p 17 ∧ p 18 ∧ p 19 ∧ p 20 ∧ p 21 ∧ p 22 ∧ p 23 ∧ p 24 ∧ p 25 ∧
    p 26 ∧ p 27 ∧ p 28 ∧ p 29 ∧ p 30 ∧ p 31 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
      h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
      h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
      h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide),
      h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide), h 24 (by decide),
      h 25 (by decide), h 26 (by decide), h 27 (by decide), h 28 (by decide), h 29 (by decide),
      h 30 (by decide), h 31 (by decide)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ i hi
    match i, hi with
    | 0, _ => exact h0 | 1, _ => exact h1 | 2, _ => exact h2 | 3, _ => exact h3
    | 4, _ => exact h4 | 5, _ => exact h5 | 6, _ => exact h6 | 7, _ => exact h7
    | 8, _ => exact h8 | 9, _ => exact h9 | 10, _ => exact h10 | 11, _ => exact h11
    | 12, _ => exact h12 | 13, _ => exact h13 | 14, _ => exact h14 | 15, _ => exact h15
    | 16, _ => exact h16 | 17, _ => exact h17 | 18, _ => exact h18 | 19, _ => exact h19
    | 20, _ => exact h20 | 21, _ => exact h21 | 22, _ => exact h22 | 23, _ => exact h23
    | 24, _ => exact h24 | 25, _ => exact h25 | 26, _ => exact h26 | 27, _ => exact h27
    | 28, _ => exact h28 | 29, _ => exact h29 | 30, _ => exact h30 | 31, _ => exact h31
    | _ + 32, h => exact absurd h (by omega)

/-- A bit of `w ||| q` where `q` (a `BitVec.ofNat`) has a zero. -/
private theorem lnk_or_bit {w : BitVec 32} {qn : Nat} (i : Nat) (h : qn / 2 ^ i % 2 = 0) :
    (w ||| BitVec.ofNat 32 qn).getLsbD i = w.getLsbD i := by
  rw [BitVec.getLsbD_or, BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq, h]
  simp

private theorem lnk_fld_or {w q : BitVec 32} {s l : Nat} : fld (w ||| q) s l = fld w s l ||| fld q s l :=
  BitVec.extractLsb'_or

private theorem lnk_fld_ofNat {qn s l : Nat} :
    (fld (BitVec.ofNat 32 qn) s l).toNat = qn % 2 ^ 32 / 2 ^ s % 2 ^ l := by
  simp only [fld, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

private theorem lnk_fld_ofNat_zero {qn s l : Nat} (h : qn % 2 ^ 32 / 2 ^ s % 2 ^ l = 0) :
    fld (BitVec.ofNat 32 qn) s l = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [lnk_fld_ofNat, h]
  rfl

/-! ### Inverting `decode` -/

private theorem lnk_ite_eq_iff {α : Type} {c : Prop} [Decidable c] {a b x : α} :
    ((if c then a else b) = x) ↔ (c ∧ a = x) ∨ (¬c ∧ b = x) := by
  by_cases hc : c <;> simp [hc]

set_option hygiene false in
/-- Split `hd : <decoder> = some i` along the decoder's branches, closing those that give
another instruction. -/
local macro "lnk_inv" : tactic => `(tactic|
  repeat' (first
    | (rw [lnk_ite_eq_iff] at hd; rcases hd with ⟨_, hd⟩ | ⟨_, hd⟩)
    | (simp only [Option.some.injEq, reduceCtorEq, Insn.ldst.injEq, and_false, false_and] at hd;
        done)
    | (simp only [decodeDPImm, decodeBranch, decodeLdSt, decodeDPReg, decodeFP] at hd)
    | (split at hd)))

private theorem lnk_inv_b {w : BitVec 32} {l : Bool} {i : BitVec 26}
    (hd : decode w = some (.b l i)) : (w &&& 0x7C000000 == 0x14000000) = true := by
  simp only [decode] at hd
  lnk_inv
  assumption

private theorem lnk_inv_adr {w : BitVec 32} {p : Bool} {i : BitVec 21} {rd : Reg}
    (hd : decode w = some (.adr p i rd)) : (w &&& 0x1F000000 == 0x10000000) = true := by
  simp only [decode] at hd
  lnk_inv
  assumption

private theorem lnk_inv_add {w : BitVec 32} {sf sub setf sh : Bool} {i : BitVec 12} {rn rd : Reg}
    (hd : decode w = some (.addSubImm sf sub setf sh i rn rd)) :
    (w &&& 0x1F800000 == 0x11000000) = true := by
  simp only [decode] at hd
  lnk_inv
  assumption

private theorem lnk_inv_ldst {w : BitVec 32} {size opc : BitVec 2} {vec : Bool} {i : BitVec 12}
    {rn rt : Reg} (hd : decode w = some (.ldst size vec opc (.uimm i) rn rt)) :
    (w &&& 0x3B000000 == 0x39000000) = true := by
  simp only [decode] at hd
  lnk_inv
  assumption

/-! ### The bits a class test fixes -/

private theorem lnk_bits_b {w : BitVec 32} (h : (w &&& 0x7C000000 == 0x14000000) = true) :
    w.getLsbD 26 = true ∧ w.getLsbD 27 = false ∧ w.getLsbD 28 = true ∧ w.getLsbD 29 = false ∧
    w.getLsbD 30 = false := by
  simp only [beq_iff_eq, BitVec.eq_of_getLsbD_eq_iff, lnk_forall_lt_32, BitVec.getLsbD_and] at h
  simpa using h

private theorem lnk_bits_adr {w : BitVec 32} (h : (w &&& 0x1F000000 == 0x10000000) = true) :
    w.getLsbD 24 = false ∧ w.getLsbD 25 = false ∧ w.getLsbD 26 = false ∧ w.getLsbD 27 = false ∧
    w.getLsbD 28 = true := by
  simp only [beq_iff_eq, BitVec.eq_of_getLsbD_eq_iff, lnk_forall_lt_32, BitVec.getLsbD_and] at h
  simpa using h

private theorem lnk_bits_add {w : BitVec 32} (h : (w &&& 0x1F800000 == 0x11000000) = true) :
    w.getLsbD 23 = false ∧ w.getLsbD 24 = true ∧ w.getLsbD 25 = false ∧ w.getLsbD 26 = false ∧
    w.getLsbD 27 = false ∧ w.getLsbD 28 = true := by
  simp only [beq_iff_eq, BitVec.eq_of_getLsbD_eq_iff, lnk_forall_lt_32, BitVec.getLsbD_and] at h
  simpa using h

private theorem lnk_bits_ldst {w : BitVec 32} (h : (w &&& 0x3B000000 == 0x39000000) = true) :
    w.getLsbD 24 = true ∧ w.getLsbD 25 = false ∧ w.getLsbD 27 = true ∧ w.getLsbD 28 = true ∧
    w.getLsbD 29 = true := by
  simp only [beq_iff_eq, BitVec.eq_of_getLsbD_eq_iff, lnk_forall_lt_32, BitVec.getLsbD_and] at h
  simpa using h

/-! ### Decoding a word of a known class -/

private theorem lnk_fwd_b {w : BitVec 32} (h26 : w.getLsbD 26 = true) (h27 : w.getLsbD 27 = false)
    (h28 : w.getLsbD 28 = true) (h29 : w.getLsbD 29 = false) (h30 : w.getLsbD 30 = false) :
    decode w = some (.b (bit w 31) (fld w 0 26)) := by
  simp only [decode, decodeBranch, fld, bit, beq_iff_eq, BitVec.eq_of_getLsbD_eq_iff,
    lnk_forall_lt_32, lnk_forall_lt_4, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb',
    Nat.reduceAdd]
  simp only [h26, h27, h28, h29, h30]
  simp

private theorem lnk_fwd_adr {w : BitVec 32} (h24 : w.getLsbD 24 = false)
    (h25 : w.getLsbD 25 = false) (h26 : w.getLsbD 26 = false) (h27 : w.getLsbD 27 = false)
    (h28 : w.getLsbD 28 = true) :
    decode w = some (.adr (bit w 31) (fld w 5 19 ++ fld w 29 2) (fld w 0 5)) := by
  simp only [decode, decodeDPImm, fld, bit, beq_iff_eq, BitVec.eq_of_getLsbD_eq_iff,
    lnk_forall_lt_32, lnk_forall_lt_4, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb',
    Nat.reduceAdd]
  simp only [h24, h25, h26, h27, h28]
  simp

private theorem lnk_fwd_add {w : BitVec 32} (h23 : w.getLsbD 23 = false)
    (h24 : w.getLsbD 24 = true) (h25 : w.getLsbD 25 = false) (h26 : w.getLsbD 26 = false)
    (h27 : w.getLsbD 27 = false) (h28 : w.getLsbD 28 = true) :
    decode w = some (.addSubImm (bit w 31) (bit w 30) (bit w 29) (bit w 22) (fld w 10 12)
      (fld w 5 5) (fld w 0 5)) := by
  simp only [decode, decodeDPImm, fld, bit, beq_iff_eq, BitVec.eq_of_getLsbD_eq_iff,
    lnk_forall_lt_32, lnk_forall_lt_4, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb',
    Nat.reduceAdd]
  simp only [h23, h24, h25, h26, h27, h28]
  simp

/-- `decodeLdSt`'s `okSingle`. -/
private def lnkOk (size : BitVec 2) (vec : Bool) (opc : BitVec 2) : Bool :=
  if vec then size = 0 || !opc.getLsbD 1
  else !(size = 3 && opc = 3) && !(size = 2 && opc = 3)

private theorem lnk_fwd_ldst {w : BitVec 32} (h24 : w.getLsbD 24 = true)
    (h25 : w.getLsbD 25 = false) (h27 : w.getLsbD 27 = true) (h28 : w.getLsbD 28 = true)
    (h29 : w.getLsbD 29 = true) :
    decode w = if lnkOk (fld w 30 2) (bit w 26) (fld w 22 2) then
      some (.ldst (fld w 30 2) (bit w 26) (fld w 22 2) (.uimm (fld w 10 12)) (fld w 5 5) (fld w 0 5))
      else none := by
  simp only [decode, decodeLdSt, lnkOk, fld, bit, beq_iff_eq, BitVec.eq_of_getLsbD_eq_iff,
    lnk_forall_lt_32, lnk_forall_lt_4, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb',
    Nat.reduceAdd]
  simp only [h24, h25, h27, h28, h29]
  simp

/-! ### Address arithmetic -/

private theorem lnk_page_toNat (x : BitVec 64) : (x &&& ~~~(0xFFF : BitVec 64)).toNat = x.toNat / 4096 * 4096 := by
  have e : x &&& ~~~(0xFFF : BitVec 64) = (x >>> 12) <<< 12 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (0xFFF : BitVec 64) = BitVec.ofNat 64 (2 ^ 12 - 1) from rfl]
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat,
      Nat.testBit_two_pow_sub_one, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hi,
      decide_true, Bool.true_and]
    by_cases h : i < 12
    · simp [h]
    · simp [h, Nat.add_sub_cancel' (Nat.le_of_not_lt h)]
  rw [e, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

private theorem lnk_call_arith (P x : BitVec 64) (h1 : -134217728 ≤ (x - P).toInt)
    (h2 : (x - P).toInt < 134217728) (h3 : (x - P).toInt % 4 = 0) :
    P + ((fld (BitVec.ofInt 32 ((x - P).toInt / 4) &&& 0x3ffffff) 0 26) ++ (0 : BitVec 2)).signExtend 64
      = x := by
  have e : ((fld (BitVec.ofInt 32 ((x - P).toInt / 4) &&& 0x3ffffff) 0 26) ++
      (0 : BitVec 2)).signExtend 64 = x - P := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by decide)]
    generalize (x - P).toInt = d at *
    have hn : (fld (BitVec.ofInt 32 (d / 4) &&& 0x3ffffff) 0 26).toNat =
        (d / 4 % ((2 ^ 32 : Nat) : Int)).toNat % 2 ^ 26 := by
      have hk : (0x3ffffff : BitVec 32).toNat = 2 ^ 26 - 1 := rfl
      rw [fld, BitVec.extractLsb'_toNat, BitVec.toNat_and, BitVec.toNat_ofInt, hk,
        Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_zero, Nat.mod_mod]
    have h0 : (0 : BitVec 2).toNat = 0 := rfl
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_append, h0, Nat.or_zero, Nat.shiftLeft_eq, hn]
    split <;> omega
  rw [e, BitVec.add_comm, BitVec.sub_add_cancel]

private theorem lnk_adrp_arith (P x : BitVec 64) (imm : BitVec 21)
    (h1 : -4294967296 ≤ (x - (P &&& ~~~(0xFFF : BitVec 64))).toInt)
    (h2 : (x - (P &&& ~~~(0xFFF : BitVec 64))).toInt < 4294967296)
    (him : imm.toNat = ((x - (P &&& ~~~(0xFFF : BitVec 64))).toInt / 16384 % 524288).toNat * 4 +
      ((x - (P &&& ~~~(0xFFF : BitVec 64))).toInt / 4096 % 4).toNat) :
    (P &&& ~~~(0xFFF : BitVec 64)) + (imm.signExtend 64 <<< 12) = x &&& ~~~(0xFFF : BitVec 64) := by
  have hc := BitVec.toInt_eq_toNat_cond (x - (P &&& ~~~(0xFFF : BitVec 64)))
  generalize (x - (P &&& ~~~(0xFFF : BitVec 64))).toInt = tt at h1 h2 him hc
  rw [BitVec.toNat_sub, lnk_page_toNat] at hc
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_signExtend,
    BitVec.toNat_setWidth, BitVec.msb_eq_decide, lnk_page_toNat, lnk_page_toNat]
  have hx := x.isLt
  have hp := P.isLt
  have hi := imm.isLt
  generalize x.toNat = X at *
  generalize P.toNat = Pn at *
  generalize imm.toNat = m at *
  simp only [Nat.reduceSub, Nat.reducePow, decide_eq_true_eq] at *
  split at hc <;> split <;> omega

private theorem lnk_lo_arith (x : BitVec 64) (k : Nat) (h : k = x.toNat % 4096) :
    (x &&& ~~~(0xFFF : BitVec 64)) + BitVec.ofNat 64 k = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, lnk_page_toNat, BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-! ### The relocated words -/

/-- `R_CALLARM64` on `BL`/`B` with a zero offset field: the linked word branches to the target. -/
theorem decode_call {w : BitVec 32} {link : Bool} {r : Reloc} {o y : Nat} {q : BitVec 32}
    (hd : decode w = some (.b link 0)) (hcall : isCallReloc r.type = true) (hoff : r.off = o)
    (hy : r.sym = some y) (hp : relocPatch base sym r o = .ok q) (hsiz : r.siz ≠ 0) :
    ∃ imm26, decode (w ||| q) = some (.b link imm26) ∧
      (base + BitVec.ofNat 64 o) + (imm26 ++ (0 : BitVec 2)).signExtend 64 =
        sym y + BitVec.ofInt 64 r.add := by
  obtain ⟨h1, h2, h3, hq⟩ := lnk_patch_call hsiz hy hcall hoff hp
  obtain ⟨b26, b27, b28, b29, b30⟩ := lnk_bits_b (lnk_inv_b hd)
  rw [lnk_fwd_b b26 b27 b28 b29 b30] at hd
  simp only [Option.some.injEq, Insn.b.injEq] at hd
  obtain ⟨hl, hz⟩ := hd
  have hqb : ∀ i, 26 ≤ i → (w ||| q).getLsbD i = w.getLsbD i := by
    intro i hi
    rw [hq, BitVec.getLsbD_or, BitVec.getLsbD_and,
      show (0x3ffffff : BitVec 32) = BitVec.ofNat 32 (2 ^ 26 - 1) from rfl,
      BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    simp only [show ¬ i < 26 by omega, decide_false, Bool.and_false, Bool.or_false]
  have hw' := lnk_fwd_b (w := w ||| q) ((hqb 26 (by omega)).trans b26)
    ((hqb 27 (by omega)).trans b27) ((hqb 28 (by omega)).trans b28)
    ((hqb 29 (by omega)).trans b29) ((hqb 30 (by omega)).trans b30)
  have e31 : bit (w ||| q) 31 = link := (hqb 31 (by omega)).trans hl
  refine ⟨fld (w ||| q) 0 26, by rw [hw', e31], ?_⟩
  rw [lnk_fld_or, hz, lnk_zero_or, hq]
  exact lnk_call_arith _ _ h1 h2 h3

/-- The bits of the `ADRP` patch. -/
private theorem lnk_hi_q {A B : Nat} (hA : A < 4) (hB : B < 524288) :
    (A * 536870912 + B * 32) / 2 ^ 24 % 2 = 0 ∧ (A * 536870912 + B * 32) / 2 ^ 25 % 2 = 0 ∧ (A * 536870912 + B * 32) / 2 ^ 26 % 2 = 0 ∧
    (A * 536870912 + B * 32) / 2 ^ 27 % 2 = 0 ∧ (A * 536870912 + B * 32) / 2 ^ 28 % 2 = 0 ∧ (A * 536870912 + B * 32) / 2 ^ 31 % 2 = 0 ∧
    (A * 536870912 + B * 32) % 2 ^ 32 / 2 ^ 0 % 2 ^ 5 = 0 ∧
    (A * 536870912 + B * 32) % 2 ^ 32 / 2 ^ 5 % 2 ^ 19 * 2 ^ 2 + (A * 536870912 + B * 32) % 2 ^ 32 / 2 ^ 29 % 2 ^ 2 = B * 4 + A := by
  simp only [Nat.reducePow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The `ADRP` of a two-word relocation: the linked word computes the target's page. -/
theorem decode_adrp {w : BitVec 32} {rd : Reg} {r : Reloc} {o y : Nat} {q : BitVec 32}
    (hd : decode w = some (.adr true 0 rd)) (hcall : isCallReloc r.type = false)
    (hoff : r.off = o) (hy : r.sym = some y) (hp : relocPatch base sym r o = .ok q)
    (hsiz : r.siz ≠ 0) :
    ∃ imm, decode (w ||| q) = some (.adr true imm rd) ∧
      ((base + BitVec.ofNat 64 o) &&& ~~~(0xFFF : BitVec 64)) + (imm.signExtend 64 <<< 12) =
        (sym y + BitVec.ofInt 64 r.add) &&& ~~~(0xFFF : BitVec 64) := by
  obtain ⟨h1, h2, A, B, hA, hB, hq, hA', hB'⟩ := lnk_patch_hi hsiz hy hcall hoff hp
  obtain ⟨b24, b25, b26, b27, b28⟩ := lnk_bits_adr (lnk_inv_adr hd)
  rw [lnk_fwd_adr b24 b25 b26 b27 b28] at hd
  simp only [Option.some.injEq, Insn.adr.injEq] at hd
  obtain ⟨h31, hz, hrd⟩ := hd
  have hQ := lnk_hi_q hA hB
  have hb : ∀ i, (A * 536870912 + B * 32) / 2 ^ i % 2 = 0 → (w ||| q).getLsbD i = w.getLsbD i := by
    intro i h; rw [hq]; exact lnk_or_bit i h
  have hfz : ∀ s l, (A * 536870912 + B * 32) % 2 ^ 32 / 2 ^ s % 2 ^ l = 0 → fld q s l = 0 := by
    intro s l h; rw [hq]; exact lnk_fld_ofNat_zero h
  have hz1 : fld w 5 19 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun v => v.getLsbD (i + 2)) hz
    simp only [BitVec.getLsbD_append, show ¬ (i + 2 < 2) by omega, ↓reduceIte,
      Nat.add_sub_cancel] at this
    rw [this]
    simp
  have hz2 : fld w 29 2 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun v => v.getLsbD i) hz
    simp only [BitVec.getLsbD_append, hi, ↓reduceIte] at this
    rw [this]
    simp
  have hw' := lnk_fwd_adr (w := w ||| q) ((hb 24 hQ.1).trans b24)
    ((hb 25 hQ.2.1).trans b25) ((hb 26 hQ.2.2.1).trans b26)
    ((hb 27 hQ.2.2.2.1).trans b27) ((hb 28 hQ.2.2.2.2.1).trans b28)
  have e31 : bit (w ||| q) 31 = true := (hb 31 hQ.2.2.2.2.2.1).trans h31
  have e0 : fld (w ||| q) 0 5 = rd := by rw [lnk_fld_or, hfz 0 5 hQ.2.2.2.2.2.2.1, lnk_or_zero]; exact hrd
  refine ⟨fld (w ||| q) 5 19 ++ fld (w ||| q) 29 2, by rw [hw', e31, e0], ?_⟩
  rw [lnk_fld_or, lnk_fld_or, hz1, hz2, lnk_zero_or, lnk_zero_or]
  apply lnk_adrp_arith _ _ _ h1 h2
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq, hq,
    lnk_fld_ofNat, lnk_fld_ofNat, ← hA', ← hB', Int.toNat_natCast, Int.toNat_natCast]
  exact hQ.2.2.2.2.2.2.2

/-- The `ADD` of `R_ADDRARM64`: the linked word adds the target's offset in its page. -/
theorem decode_addLo {w : BitVec 32} {rn rd : Reg} {r : Reloc} {o y : Nat} {q : BitVec 32}
    (hd : decode w = some (.addSubImm true false false false 0 rn rd))
    (hty : r.type = "R_ADDRARM64") (hoff : r.off = o) (hy : r.sym = some y)
    (hp : relocPatch base sym r (o + 4) = .ok q) (hsiz : r.siz ≠ 0) :
    ∃ imm12, decode (w ||| q) = some (.addSubImm true false false false imm12 rn rd) ∧
      ((sym y + BitVec.ofInt 64 r.add) &&& ~~~(0xFFF : BitVec 64)) + imm12.setWidth 64 =
        sym y + BitVec.ofInt 64 r.add := by
  have hcall : isCallReloc r.type = false := by rw [hty]; decide
  have hsc : (if r.type == "R_ADDRARM64" then some 0 else ldstScale r.type) = some 0 := by
    simp [hty]
  obtain ⟨k, hk, hk4, hq⟩ := lnk_patch_lo hsiz hy hcall hsc hoff hp
  obtain ⟨b23, b24, b25, b26, b27, b28⟩ := lnk_bits_add (lnk_inv_add hd)
  rw [lnk_fwd_add b23 b24 b25 b26 b27 b28] at hd
  simp only [Option.some.injEq, Insn.addSubImm.injEq] at hd
  obtain ⟨h31, h30, h29, h22, hz, hrn, hrd⟩ := hd
  have hb : ∀ i, k * 1024 / 2 ^ i % 2 = 0 → (w ||| q).getLsbD i = w.getLsbD i := by
    intro i h; rw [hq]; exact lnk_or_bit i h
  have hfz : ∀ s l, k * 1024 % 2 ^ 32 / 2 ^ s % 2 ^ l = 0 → fld q s l = 0 := by
    intro s l h; rw [hq]; exact lnk_fld_ofNat_zero h
  have hw' := lnk_fwd_add (w := w ||| q) ((hb 23 (by omega)).trans b23)
    ((hb 24 (by omega)).trans b24) ((hb 25 (by omega)).trans b25)
    ((hb 26 (by omega)).trans b26) ((hb 27 (by omega)).trans b27)
    ((hb 28 (by omega)).trans b28)
  have e31 : bit (w ||| q) 31 = true := (hb 31 (by omega)).trans h31
  have e30 : bit (w ||| q) 30 = false := (hb 30 (by omega)).trans h30
  have e29 : bit (w ||| q) 29 = false := (hb 29 (by omega)).trans h29
  have e22 : bit (w ||| q) 22 = false := (hb 22 (by omega)).trans h22
  have e5 : fld (w ||| q) 5 5 = rn := by rw [lnk_fld_or, hfz 5 5 (by omega), lnk_or_zero]; exact hrn
  have e0 : fld (w ||| q) 0 5 = rd := by rw [lnk_fld_or, hfz 0 5 (by omega), lnk_or_zero]; exact hrd
  refine ⟨fld (w ||| q) 10 12, by rw [hw', e31, e30, e29, e22, e5, e0], ?_⟩
  have e : (fld (w ||| q) 10 12).setWidth 64 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    rw [lnk_fld_or, hz, lnk_zero_or, BitVec.toNat_setWidth, hq, lnk_fld_ofNat, BitVec.toNat_ofNat]
    omega
  rw [e]
  exact lnk_lo_arith _ _ (by omega)

/-- The load/store of `R_ARM64_PCREL_LDST*`: the linked word's scaled offset is the target's
offset in its page. -/
theorem decode_ldstLo {w : BitVec 32} {size opc : BitVec 2} {rn rt : Reg} {r : Reloc} {o y : Nat}
    {q : BitVec 32} (hd : decode w = some (.ldst size false opc (.uimm 0) rn rt))
    (hsc : ldstScale r.type = some size.toNat) (hoff : r.off = o) (hy : r.sym = some y)
    (hp : relocPatch base sym r (o + 4) = .ok q) (hsiz : r.siz ≠ 0) :
    ∃ imm12, decode (w ||| q) = some (.ldst size false opc (.uimm imm12) rn rt) ∧
      ((sym y + BitVec.ofInt 64 r.add) &&& ~~~(0xFFF : BitVec 64)) +
          BitVec.ofNat 64 (imm12.toNat * 2 ^ size.toNat) =
        sym y + BitVec.ofInt 64 r.add := by
  have hcall : isCallReloc r.type = false := by
    cases hk : isCallReloc r.type
    · rfl
    · exfalso
      simp only [isCallReloc, Bool.or_eq_true, beq_iff_eq] at hk
      rcases hk with hk | hk <;> rw [hk] at hsc <;> simp [ldstScale] at hsc
  have hA : (r.type == "R_ADDRARM64") = false := by
    cases hk : (r.type == "R_ADDRARM64")
    · rfl
    · exfalso
      simp only [beq_iff_eq] at hk
      rw [hk] at hsc
      simp [ldstScale] at hsc
  have hsc' : (if r.type == "R_ADDRARM64" then some 0 else ldstScale r.type) = some size.toNat := by
    simp only [hA, Bool.false_eq_true, ↓reduceIte, hsc]
  obtain ⟨k, hk, hk4, hq⟩ := lnk_patch_lo hsiz hy hcall hsc' hoff hp
  obtain ⟨b24, b25, b27, b28, b29⟩ := lnk_bits_ldst (lnk_inv_ldst hd)
  rw [lnk_fwd_ldst b24 b25 b27 b28 b29] at hd
  split at hd
  · rename_i hok
    simp only [Option.some.injEq, Insn.ldst.injEq, AMode.uimm.injEq] at hd
    obtain ⟨hs, hv, ho, hz, hrn, hrt⟩ := hd
    have hb : ∀ i, k * 1024 / 2 ^ i % 2 = 0 → (w ||| q).getLsbD i = w.getLsbD i := by
      intro i h; rw [hq]; exact lnk_or_bit i h
    have hfz : ∀ s l, k * 1024 % 2 ^ 32 / 2 ^ s % 2 ^ l = 0 → fld q s l = 0 := by
      intro s l h; rw [hq]; exact lnk_fld_ofNat_zero h
    have hw' := lnk_fwd_ldst (w := w ||| q) ((hb 24 (by omega)).trans b24)
      ((hb 25 (by omega)).trans b25) ((hb 27 (by omega)).trans b27)
      ((hb 28 (by omega)).trans b28) ((hb 29 (by omega)).trans b29)
    have e30 : fld (w ||| q) 30 2 = size := by
      rw [lnk_fld_or, hfz 30 2 (by omega), lnk_or_zero]; exact hs
    have e26 : bit (w ||| q) 26 = false := (hb 26 (by omega)).trans hv
    have e22 : fld (w ||| q) 22 2 = opc := by
      rw [lnk_fld_or, hfz 22 2 (by omega), lnk_or_zero]; exact ho
    have e5 : fld (w ||| q) 5 5 = rn := by
      rw [lnk_fld_or, hfz 5 5 (by omega), lnk_or_zero]; exact hrn
    have e0 : fld (w ||| q) 0 5 = rt := by
      rw [lnk_fld_or, hfz 0 5 (by omega), lnk_or_zero]; exact hrt
    rw [hs, hv, ho] at hok
    refine ⟨fld (w ||| q) 10 12, by rw [hw', e30, e26, e22, e5, e0]; simp only [hok, ↓reduceIte], ?_⟩
    have e : (fld (w ||| q) 10 12).toNat = k := by
      rw [lnk_fld_or, hz, lnk_zero_or, hq, lnk_fld_ofNat]
      omega
    rw [e]
    exact lnk_lo_arith _ _ hk
  · cases hd

end GoFV.Proof.Obj
