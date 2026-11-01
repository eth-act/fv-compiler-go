import GoFV.Opt.KnownBitsCheck
import Std.Tactic.BVDecide

/-!
# Known bits on 64-bit patterns (issue #26)

The 64-bit identities behind the soundness of known bits' transfer functions
(`GoFV.Opt.KnownBits.tk`, `doShift`, `norm`, `incl`): `Agree r z` (`z` has the bits `r` claims),
`AgreeLo n r z` (on the low `n` bits). Each is proved once for 64-bit patterns (integers
sign-extended from their width, booleans 0/1), by `bv_decide` on bitwise formulas.
-/

namespace GoFV.Proof.KnownBits

open GoFV.Opt.KnownBits

/-- `z` has the bits `r` claims. -/
def Agree (r : BB) (z : BitVec 64) : Prop := (z ^^^ r.1) &&& r.2 = 0

/-- `z` has the bits `r` claims among its low `n`. -/
def AgreeLo (n : Nat) (r : BB) (z : BitVec 64) : Prop := ((z ^^^ r.1) &&& r.2).setWidth n = 0

/-- An entry's value has no bit it does not claim known. -/
def Masked (r : BB) : Prop := r.1 &&& ~~~r.2 = 0

theorem Agree.lo {r : BB} {z : BitVec 64} (h : Agree r z) (n : Nat) : AgreeLo n r z := by
  unfold AgreeLo; rw [h]; simp

theorem agree_zero (v z : BitVec 64) : Agree (v, 0) z := by simp [Agree]

theorem incl_spec {r e : BB} (h : incl r e = true) : e.2 &&& ~~~r.2 = 0 ∧ r.1 &&& e.2 = e.1 &&& e.2 := by
  simpa [incl] using h

theorem Agree.incl {r e : BB} {z : BitVec 64} (h : incl r e = true) (hz : Agree r z) : Agree e z := by
  obtain ⟨h1, h2⟩ := incl_spec h
  obtain ⟨v, k⟩ := r; obtain ⟨v', k'⟩ := e
  simp only [Agree] at *
  bv_decide

theorem incl_known_zero {v e1 e2 : BitVec 64} (h : incl (v, 0) (e1, e2) = true) : e2 = 0 := by
  have := (incl_spec h).1; simp only at this; bv_decide

theorem ent_masked (E : Array (Int64 × Int64)) (a : GoFV.SSA.ID) : Masked (ent E a) := by
  simp only [Masked, ent]; bv_decide

/-! ## Bitwise families -/

theorem agree_and {a ak b bk X Y : BitVec 64} (ha : Agree (a, ak) X) (hb : Agree (b, bk) Y)
    (ma : Masked (a, ak)) (mb : Masked (b, bk)) :
    Agree (a &&& b, (a &&& b) ||| (~~~a &&& ak) ||| (~~~b &&& bk)) (X &&& Y) := by
  simp only [Agree, Masked] at *; bv_decide

theorem agree_or {a ak b bk X Y : BitVec 64} (ha : Agree (a, ak) X) (hb : Agree (b, bk) Y)
    (ma : Masked (a, ak)) (mb : Masked (b, bk)) :
    Agree (a ||| b, a ||| b ||| (~~~a &&& ~~~b &&& (ak &&& bk))) (X ||| Y) := by
  simp only [Agree, Masked] at *; bv_decide

theorem agree_xor {a ak b bk X Y : BitVec 64} (ha : Agree (a, ak) X) (hb : Agree (b, bk) Y) :
    Agree (a ^^^ b, ak &&& bk) (X ^^^ Y) := by
  simp only [Agree] at *; bv_decide

theorem agree_not {a ak X : BitVec 64} (ha : Agree (a, ak) X) : Agree (~~~a, ak) (~~~X) := by
  simp only [Agree] at *; bv_decide

/-- `AndB` with a `false` side: the other side's entry is only masked. -/
theorem agreeLo_and_false_l {a ak b bk : BitVec 64} (ha : Agree (a, ak) 0) (mb : Masked (b, bk))
    (ma : Masked (a, ak)) :
    AgreeLo 1 (a &&& b, (a &&& b) ||| (~~~a &&& ak) ||| (~~~b &&& bk)) 0 := by
  simp only [Agree, AgreeLo, Masked] at *; bv_decide

theorem agreeLo_and_false_r {a ak b bk : BitVec 64} (hb : Agree (b, bk) 0) (mb : Masked (b, bk))
    (ma : Masked (a, ak)) :
    AgreeLo 1 (a &&& b, (a &&& b) ||| (~~~a &&& ak) ||| (~~~b &&& bk)) 0 := by
  simp only [Agree, AgreeLo, Masked] at *; bv_decide

theorem agreeLo_or_true_l {a ak b bk : BitVec 64} (ha : Agree (a, ak) 1) (mb : Masked (b, bk))
    (ma : Masked (a, ak)) :
    AgreeLo 1 (a ||| b, a ||| b ||| (~~~a &&& ~~~b &&& (ak &&& bk))) 1 := by
  simp only [Agree, AgreeLo, Masked] at *; bv_decide

theorem agreeLo_or_true_r {a ak b bk : BitVec 64} (hb : Agree (b, bk) 1) (mb : Masked (b, bk))
    (ma : Masked (a, ak)) :
    AgreeLo 1 (a ||| b, a ||| b ||| (~~~a &&& ~~~b &&& (ak &&& bk))) 1 := by
  simp only [Agree, AgreeLo, Masked] at *; bv_decide

/-- `Not` of a boolean pattern: bit 0 of the complement. -/
theorem agreeLo_not_bool {a ak : BitVec 64} (b : Bool) (ha : Agree (a, ak) (if b then 1 else 0)) :
    AgreeLo 1 (~~~a, ak) (if !b then 1 else 0) := by
  cases b <;> simp only [Agree, AgreeLo, Bool.not_true, Bool.not_false] at * <;> bv_decide

/-! ## Comparisons -/

/-- Two patterns with a known bit that differs are different. -/
theorem ne_of_known {a ak b bk X Y : BitVec 64} (ha : Agree (a, ak) X) (hb : Agree (b, bk) Y)
    (h : (a ^^^ b) &&& ak &&& bk ≠ 0) : X ≠ Y := by
  intro hXY; subst hXY; simp only [Agree] at *; apply h; bv_decide

/-- Fully known patterns are their entries' values. -/
theorem eq_of_full {a X : BitVec 64} (ha : Agree (a, BitVec.allOnes 64) X) : X = a := by
  simp only [Agree] at *; bv_decide

theorem agree_eq {a ak b bk X Y : BitVec 64} (ha : Agree (a, ak) X) (hb : Agree (b, bk) Y) :
    Agree (if (a ^^^ b) &&& ak &&& bk != 0 then (0, BitVec.allOnes 64)
      else if ak == BitVec.allOnes 64 && bk == BitVec.allOnes 64 then
        (if a == b then 1 else 0, BitVec.allOnes 64)
      else (0, ~~~1)) (if X == Y then 1 else 0) := by
  by_cases h1 : (a ^^^ b) &&& ak &&& bk = 0
  · by_cases h2 : ak = BitVec.allOnes 64 ∧ bk = BitVec.allOnes 64
    · obtain ⟨rfl, rfl⟩ := h2
      rw [eq_of_full ha, eq_of_full hb]
      simp only [h1, bne_self_eq_false, Bool.false_eq_true, ite_false, beq_self_eq_true,
        Bool.and_self, ite_true]
      simp [Agree]
    · have h2' : (ak == BitVec.allOnes 64 && bk == BitVec.allOnes 64) = false := by
        simpa [Bool.and_eq_true, beq_iff_eq] using h2
      simp only [h1, bne_self_eq_false, Bool.false_eq_true, ite_false, h2']
      simp only [Agree]; split <;> bv_decide
  · have hne := ne_of_known ha hb h1
    have h1' : ((a ^^^ b) &&& ak &&& bk != 0) = true := by simpa using h1
    simp only [h1', ite_true, beq_iff_eq, hne]
    simp [Agree]

theorem agree_neq {a ak b bk X Y : BitVec 64} (ha : Agree (a, ak) X) (hb : Agree (b, bk) Y) :
    Agree (if (a ^^^ b) &&& ak &&& bk != 0 then (1, BitVec.allOnes 64)
      else if ak == BitVec.allOnes 64 && bk == BitVec.allOnes 64 then
        (if a != b then 1 else 0, BitVec.allOnes 64)
      else (0, ~~~1)) (if X != Y then 1 else 0) := by
  by_cases h1 : (a ^^^ b) &&& ak &&& bk = 0
  · by_cases h2 : ak = BitVec.allOnes 64 ∧ bk = BitVec.allOnes 64
    · obtain ⟨rfl, rfl⟩ := h2
      rw [eq_of_full ha, eq_of_full hb]
      simp only [h1, bne_self_eq_false, Bool.false_eq_true, ite_false, beq_self_eq_true,
        Bool.and_self, ite_true]
      simp [Agree]
    · have h2' : (ak == BitVec.allOnes 64 && bk == BitVec.allOnes 64) = false := by
        simpa [Bool.and_eq_true, beq_iff_eq] using h2
      simp only [h1, bne_self_eq_false, Bool.false_eq_true, ite_false, h2']
      simp only [Agree]; split <;> bv_decide
  · have hne := ne_of_known ha hb h1
    have h1' : ((a ^^^ b) &&& ak &&& bk != 0) = true := by simpa using h1
    simp only [h1', ite_true, bne_iff_ne, ne_eq, hne, not_false_eq_true]
    simp [Agree]

end GoFV.Proof.KnownBits
