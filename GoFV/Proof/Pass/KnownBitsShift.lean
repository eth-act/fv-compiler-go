import GoFV.Proof.Pass.KnownBitsDomain

/-!
# Soundness of known bits' shift transfer functions (issue #26)

A shift by an amount whose entry is `(y, yk)` is checked against every effective amount
`m ≤ w` (`min` of the amount and the operand width) the entry allows (`feasible`). `feasible_of`:
the run's effective amount is among them; `doShift_sound`: the shift by `m` has, on the bits of
its width, the bits `doShift` claims. `shift_sound` combines them with `norm_retype`.
-/

namespace GoFV.Proof.KnownBits

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.KnownBits

theorem sshift_rep {n : Nat} (x : BitVec n) (m : Nat) (h0 : 0 < n) (h2 : n ≤ 64) :
    ((x.signExtend 64).sshiftRight m).setWidth n = x.sshiftRight m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend, BitVec.msb_signExtend, hi, decide_true, Bool.true_and]
  have h5 : ¬ 64 ≤ i := by omega
  have h6 : ¬ n ≤ i := by omega
  by_cases h3 : m + i < n
  · have h4 : m + i < 64 := by omega
    simp [h3, h4, h5, h6]
  · by_cases h4 : m + i < 64
    · simp [h3, h4, h5, h6]
    · by_cases h7 : 64 ≤ n
      · have : n = 64 := by omega
        subst this; simp [h3, h4, h5, h6, BitVec.msb_eq_getMsbD_zero]
      · simp [h3, h4, h5, h6, h7]
theorem zext64 {n : Nat} (x : BitVec n) (h2 : n ≤ 64) :
    x.setWidth 64 = x.signExtend 64 &&& lowMask n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [lowMask, BitVec.getLsbD_signExtend, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, BitVec.getLsbD_setWidth]
  by_cases h4 : i < n <;> simp [h4, hi]
  have : i - n < 64 := by omega
  simp [this, BitVec.getLsbD_of_ge x i (by omega)]

theorem and_not_of_shift_and (A K O : BitVec 64) (h1 : A &&& K = 0) (h2 : A &&& O = A) :
    A &&& (K ||| ~~~O) = 0 := by bv_decide

theorem lsh_core (Y ak : BitVec 64) (m : Nat) (h : Y &&& ak = 0) :
    (Y <<< m) &&& ((ak <<< m) ||| lowMask m) = 0 := by
  unfold lowMask
  refine and_not_of_shift_and _ _ _ ?_ ?_
  · rw [← BitVec.shiftLeft_and_distrib, h]; simp
  · rw [← BitVec.shiftLeft_and_distrib, BitVec.and_allOnes]

theorem rshu_pre (Y ak L : BitVec 64) (h : Y &&& ak = 0) : (Y &&& L) &&& (ak ||| ~~~L) = 0 := by
  bv_decide

theorem rshu_core (Y ak L : BitVec 64) (m : Nat) (h : Y &&& ak = 0) :
    ((Y &&& L) >>> m) &&& (((ak ||| ~~~L) >>> m) ||| ~~~(BitVec.allOnes 64 >>> m)) = 0 := by
  refine and_not_of_shift_and _ _ _ ?_ ?_
  · rw [← BitVec.ushiftRight_and_distrib, rshu_pre Y ak L h]; simp
  · rw [← BitVec.ushiftRight_and_distrib, BitVec.and_allOnes]

theorem xor_and_mask (X a L : BitVec 64) : (X &&& L) ^^^ (a &&& L) = (X ^^^ a) &&& L := by
  bv_decide

theorem agree_xor_and {a ak X : BitVec 64} (h : Agree (a, ak) X) : (X ^^^ a) &&& ak = 0 := h

/-- The shift of an `w`-bit `x` with entry `r` by `m ≤ w`. -/
def shiftVal (s : ShK) {w : Width} (x : BitVec w.bits) (m : Nat) : BitVec w.bits :=
  match s with
  | .lsh => x <<< m
  | .rshu => x >>> m
  | .rsh => x.sshiftRight m

theorem doShift_sound (s : ShK) (w : Width) (x : BitVec w.bits) {r : BB} (m : Nat)
    (hm : m ≤ w.bits) (h : Agree r (x.signExtend 64)) :
    GamLo (doShift s w r m) (.int w (shiftVal s x m)) := by
  obtain ⟨a, ak⟩ := r
  have hw := width_le w
  have h0 := width_pos w
  refine .inr (.inr (.inl ⟨w, _, rfl, ?_⟩))
  have hX := setWidth_signExtend_of_le x (Nat.le_refl _) hw
  rw [BitVec.setWidth_eq] at hX
  unfold AgreeLo
  cases s with
  | lsh =>
    simp only [doShift, shiftVal]
    split
    · dsimp only
      rw [BitVec.setWidth_and, BitVec.setWidth_xor,
        setWidth_signExtend_of_le (x <<< m) (Nat.le_refl _) hw, BitVec.setWidth_eq,
        ← hX, ← BitVec.setWidth_shiftLeft_of_le hw, ← BitVec.setWidth_xor,
        ← BitVec.setWidth_and, ← BitVec.shiftLeft_xor_distrib,
        lsh_core _ _ _ (agree_xor_and h)]
      simp
    · rw [BitVec.shiftLeft_eq_zero (by omega)]; simp [BitVec.signExtend]
  | rshu =>
    simp only [doShift, shiftVal]
    split
    · have hz : (x >>> m).setWidth 64 = (x.signExtend 64 &&& lowMask w.bits) >>> m := by
        rw [← zext64 x hw, BitVec.setWidth_ushiftRight hw]
      dsimp only
      rw [BitVec.setWidth_and, BitVec.setWidth_xor,
        setWidth_signExtend_of_le (x >>> m) (Nat.le_refl _) hw,
        ← BitVec.setWidth_setWidth_of_le (x >>> m) hw, hz,
        ← BitVec.setWidth_xor, ← BitVec.setWidth_and, ← BitVec.ushiftRight_xor_distrib,
        xor_and_mask, rshu_core _ _ _ _ (agree_xor_and h)]
      simp
    · rw [BitVec.ushiftRight_eq_zero (by omega)]; simp [BitVec.signExtend]
  | rsh =>
    simp only [doShift, shiftVal]
    rw [BitVec.setWidth_and, BitVec.setWidth_xor,
      setWidth_signExtend_of_le (x.sshiftRight m) (Nat.le_refl _) hw, BitVec.setWidth_eq,
      ← sshift_rep x m h0 hw, ← BitVec.setWidth_xor, ← BitVec.setWidth_and,
      ← BitVec.sshiftRight_xor_distrib, ← BitVec.sshiftRight_and_distrib, agree_xor_and h]
    simp


theorem feasible_lt_core (Z y yk L : BitVec 64) (h : (Z ^^^ y) &&& yk = 0) :
    ((Z &&& L) ^^^ y) &&& yk &&& L = 0 := by bv_decide

theorem feasible_ge_core (Z y yk L : BitVec 64) (h : (Z ^^^ y) &&& yk = 0) :
    (Z &&& L) &&& (((y &&& yk) ||| ~~~yk) &&& L) = Z &&& L := by bv_decide

/-- The run's effective shift amount is one the checker considers. -/
theorem feasible_of (w a : Width) (bounded : Bool) {y yk : BitVec 64} (S : BitVec a.bits)
    (h : Agree (y, yk) (S.signExtend 64)) (hnp : ¬(bounded = true ∧ w.bits ≤ S.toNat)) :
    feasible w a bounded y yk (min S.toNat w.bits) = true := by
  have hz := zext64 S (width_le a)
  unfold feasible
  by_cases hlt : S.toNat < w.bits
  · rw [Nat.min_eq_left (Nat.le_of_lt hlt)]
    simp only [hlt, ↓reduceIte]
    rw [BitVec.ofNat_toNat, hz]
    simpa using feasible_lt_core _ y yk (lowMask a.bits) h
  · rw [Nat.min_eq_right (by omega)]
    simp only [Nat.lt_irrefl, ↓reduceIte]
    have hb : bounded = false := by
      cases bounded
      · rfl
      · exact absurd ⟨rfl, by omega⟩ hnp
    simp only [hb, Bool.not_false, Bool.true_and, decide_eq_true_eq]
    have hS : S.toNat = (S.signExtend 64 &&& lowMask a.bits).toNat := by
      rw [← hz, BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
      exact Nat.lt_of_lt_of_le S.isLt (Nat.pow_le_pow_right (by decide) (width_le a))
    have := feasible_ge_core (S.signExtend 64) y yk (lowMask a.bits) h
    calc w.bits ≤ S.toNat := by omega
      _ = ((S.signExtend 64 &&& lowMask a.bits) &&& (((y &&& yk) ||| ~~~yk) &&& lowMask a.bits)).toNat := by
          rw [this, hS]
      _ ≤ _ := by rw [BitVec.toNat_and]; exact Nat.and_le_right

theorem sem_shift (s : ShK) (w a : Width) (ai : Int64) (l : List Val) :
    sem (.shift s w a) ai l = Shift.shift w a (ai == 1) (shiftVal s) l := by
  cases s <;> rfl

/-- **Soundness of the shift check.** -/
theorem shift_sound (s : ShK) (w a : Width) (ai : Int64) {r0 r1 e : BB} (t : Ty) (l : List Val)
    (hl : ∀ i (h : i < l.length), i < 2 → Gam (if i = 0 then r0 else r1) l[i])
    (hok : shiftOK t s w a (ai == 1) r0 r1 e = true) :
    Gam e ((sem (.shift s w a) ai l).retype t) := by
  rw [sem_shift]
  match l with
  | [x, y] =>
    have h0 := hl 0 (by simp) (by decide); have h1 := hl 1 (by simp) (by decide)
    simp only [ite_true, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    simp only [Nat.one_ne_zero, ite_false] at h1
    cases hx : x.asInt w with
    | none => simp only [Shift.shift, hx]; exact .inl (by cases t <;> rfl)
    | some X =>
      cases hy : y.asInt a with
      | none => simp only [Shift.shift, hx, hy]; exact .inl (by cases t <;> rfl)
      | some S =>
        simp only [Shift.shift, hx, hy]
        split
        · exact .inl (by cases t <;> rfl)
        · rename_i hnp
          rw [asInt_some hx] at h0; rw [asInt_some hy] at h1
          obtain ⟨y1, yk⟩ := r1
          have hf := feasible_of w a (ai == 1) S h1.int (by simpa using hnp)
          have hm : min S.toNat w.bits ≤ w.bits := Nat.min_le_right _ _
          have hall := List.all_eq_true.1 hok (min S.toNat w.bits) (List.mem_range.2 (by omega))
          simp only [hf, Bool.not_true, Bool.false_or] at hall
          exact (norm_retype (doShift_sound s w X _ hm h0.int) t).incl hall
  | [] => simp only [Shift.shift]; exact .inl (by cases t <;> rfl)
  | [_] => simp only [Shift.shift]; exact .inl (by cases t <;> rfl)
  | _ :: _ :: _ :: _ => simp only [Shift.shift]; exact .inl (by cases t <;> rfl)

end GoFV.Proof.KnownBits
