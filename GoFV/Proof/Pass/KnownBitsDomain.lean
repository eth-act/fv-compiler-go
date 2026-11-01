import GoFV.Proof.Pass.KnownBitsCore
import GoFV.Proof.Pass.KnownBitsKind
import GoFV.Proof.Retype

/-!
# Soundness of known bits' transfer functions on values (issue #26)

`Gam r y`: the value `y` has the bits the entry `r` claims (`rep`: integers sign-extended to 64
bits, booleans 0/1; `poison` and any value when nothing is claimed). `GamLo` claims only the
low bits of the value's width; `norm_retype` turns it into `Gam` of the entry normalised at the
shape the value takes (`Val.retype`). `tk_sound`: each non-shift family's transfer function on
entries its arguments have gives an entry its result has.
-/

namespace GoFV.Proof.KnownBits

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.KnownBits

/-- The 64-bit pattern of an integer or boolean. -/
def rep : Val → Option (BitVec 64)
  | .int _ z => some (z.signExtend 64)
  | .bool b => some (if b then 1 else 0)
  | _ => none

/-- `y` has the bits `r` claims. -/
def Gam (r : BB) (y : Val) : Prop := y = .poison ∨ r.2 = 0 ∨ ∃ z, rep y = some z ∧ Agree r z

/-- `y` has the bits `r` claims among the bits of its width. -/
def GamLo (r : BB) (y : Val) : Prop :=
  y = .poison ∨ r.2 = 0 ∨ (∃ w z, y = .int w z ∧ AgreeLo w.bits r (z.signExtend 64)) ∨
    ∃ b, y = .bool b ∧ AgreeLo 1 r (if b then 1 else 0)

theorem Gam.poison (r : BB) : Gam r .poison := .inl rfl

theorem Gam.lo {r : BB} {y : Val} (h : Gam r y) : GamLo r y := by
  rcases h with h | h | ⟨z, hz, ha⟩
  · exact .inl h
  · exact .inr (.inl h)
  · cases y with
    | int w x => cases hz; exact .inr (.inr (.inl ⟨w, x, rfl, ha.lo _⟩))
    | bool b => cases hz; exact .inr (.inr (.inr ⟨b, rfl, ha.lo _⟩))
    | _ => cases hz

theorem Gam.incl {r e : BB} {y : Val} (h : incl r e = true) (hy : Gam r y) : Gam e y := by
  rcases hy with hy | hy | ⟨z, hz, ha⟩
  · exact .inl hy
  · obtain ⟨v, k⟩ := r; obtain ⟨e1, e2⟩ := e
    simp only at hy; subst hy
    exact .inr (.inl (incl_known_zero h))
  · exact .inr (.inr ⟨z, hz, ha.incl h⟩)

theorem Gam.int {r : BB} {w : Width} {x : BitVec w.bits} (h : Gam r (.int w x)) :
    Agree r (x.signExtend 64) := by
  rcases h with h | h | ⟨z, hz, ha⟩
  · cases h
  · obtain ⟨v, k⟩ := r; simp only at h; subst h; exact agree_zero _ _
  · cases hz; exact ha

theorem Gam.bool {r : BB} {b : Bool} (h : Gam r (.bool b)) : Agree r (if b then 1 else 0) := by
  rcases h with h | h | ⟨z, hz, ha⟩
  · cases h
  · obtain ⟨v, k⟩ := r; simp only at h; subst h; exact agree_zero _ _
  · cases hz; exact ha

/-! ## Normalisation at a shape -/

theorem setWidth_signExtend_of_le {n m : Nat} (z : BitVec n) (h1 : m ≤ n) (h2 : n ≤ 64) :
    (z.signExtend 64).setWidth m = z.setWidth m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h3 : i < 64 := by omega
  have h4 : i < n := by omega
  simp [BitVec.getElem_signExtend, hi, h3, h4]

theorem xor_and_and (Z v k : BitVec 64) : (Z ^^^ (v &&& k)) &&& k = (Z ^^^ v) &&& k := by
  bv_decide

theorem norm_int_agree' {n n' : Nat} (z : BitVec n) (v k : BitVec 64) (hle : n' ≤ n) (h64 : n ≤ 64)
    (h : ((z.signExtend 64 ^^^ v) &&& k).setWidth n = 0) :
    (((z.setWidth n').signExtend 64 ^^^ ((v.setWidth n').signExtend 64 &&&
      (k.setWidth n').signExtend 64)) &&& (k.setWidth n').signExtend 64) = 0 := by
  rw [← setWidth_signExtend_of_le z hle h64, ← BitVec.signExtend_and, ← BitVec.signExtend_xor,
    ← BitVec.signExtend_and, ← BitVec.setWidth_and, ← BitVec.setWidth_xor,
    ← BitVec.setWidth_and, xor_and_and, ← BitVec.setWidth_setWidth_of_le _ hle, h]
  simp [BitVec.signExtend]

theorem width_le (w : Width) : w.bits ≤ 64 := by cases w <;> decide

theorem norm_int_agree (w w' : Width) (z : BitVec w.bits) (r : BB) (hle : w'.bits ≤ w.bits)
    (h : AgreeLo w.bits r (z.signExtend 64)) :
    Agree (norm (.int w') r) ((z.setWidth w'.bits).signExtend 64) := by
  obtain ⟨v, k⟩ := r
  simp only [AgreeLo, Agree, norm, sext] at *
  exact norm_int_agree' z v k hle (width_le w) h

theorem norm_bool_agree (b : Bool) (r : BB) (h : AgreeLo 1 r (if b then 1 else 0)) :
    Agree (norm .bool r) (if b then 1 else 0) := by
  obtain ⟨v, k⟩ := r
  cases b <;> simp only [AgreeLo, Agree, norm] at * <;> bv_decide

theorem retype_int_int (w w' : Width) (z : BitVec w.bits) :
    (Val.int w z).retype (.int w') =
      if w'.bits ≤ w.bits then .int w' (z.setWidth w'.bits) else .poison := by
  simp [Val.retype]

theorem norm_int_known_zero (w : Width) (v : BitVec 64) : (norm (.int w) (v, 0)).2 = 0 := by
  simp [norm, sext, BitVec.signExtend]

/-- **Normalisation**: a value with the low bits an entry claims has, at any shape, the bits of
the normalised entry. -/
theorem norm_retype {r : BB} {y : Val} (h : GamLo r y) (t : Ty) : Gam (norm t r) (y.retype t) := by
  rcases h with h | h | ⟨w, z, rfl, ha⟩ | ⟨b, rfl, ha⟩
  · subst h; cases t <;> exact .inl rfl
  · obtain ⟨v, k⟩ := r; simp only at h; subst h
    cases t with
    | bool =>
      have hb := Val.retype_hasTy .bool y
      generalize y.retype .bool = y' at hb ⊢
      cases y' <;> simp [Val.hasTy] at hb
      · rename_i b
        refine .inr (.inr ⟨_, rfl, ?_⟩)
        cases b <;> simp only [Agree, norm] <;> bv_decide
      · exact .inl rfl
    | int w => exact .inr (.inl (norm_int_known_zero w v))
    | _ => exact .inr (.inl rfl)
  · cases t with
    | int w' =>
      rw [retype_int_int]
      split
      · exact .inr (.inr ⟨_, rfl, norm_int_agree w w' z r (by assumption) ha⟩)
      · exact .inl rfl
    | bool => exact .inl rfl
    | _ => exact .inr (.inl rfl)
  · cases t with
    | bool => exact .inr (.inr ⟨_, rfl, norm_bool_agree b r ha⟩)
    | int w => exact .inl rfl
    | _ => exact .inr (.inl rfl)

/-- An atom's register: the normalised empty entry holds any value at the shape. -/
theorem gam_any {e : BB} (t : Ty) (h : incl (norm t (0, 0)) e = true) (y : Val) :
    Gam e (y.retype t) :=
  (norm_retype (r := (0, 0)) (.inr (.inl rfl)) t).incl h

/-! ## Argument values -/

theorem asInt_some {w : Width} {a : Val} {x : BitVec w.bits} (h : a.asInt w = some x) :
    a = .int w x := by
  cases a with
  | int w' x' =>
    simp only [Val.asInt] at h
    split at h
    · rename_i hw; subst hw; cases h; rfl
    · cases h
  | _ => simp [Val.asInt] at h

theorem asBool_some {a : Val} {b : Bool} (h : a.asBool = some b) : a = .bool b := by
  cases a <;> simp [Val.asBool] at h; subst h; rfl

theorem width_pos (w : Width) : 0 < w.bits := by cases w <;> decide

theorem signExtend_inj (w : Width) (x y : BitVec w.bits) :
    (x.signExtend 64 == y.signExtend 64) = (x == y) := by
  by_cases h : x = y
  · subst h; simp only [beq_self_eq_true]
  · have : x.signExtend 64 ≠ y.signExtend 64 := fun he => h (by
      have := congrArg (BitVec.setWidth w.bits) he
      rwa [setWidth_signExtend_of_le x (Nat.le_refl _) (width_le w),
        setWidth_signExtend_of_le y (Nat.le_refl _) (width_le w), BitVec.setWidth_eq,
        BitVec.setWidth_eq] at this)
    rw [beq_eq_false_iff_ne.2 this, beq_eq_false_iff_ne.2 h]

theorem signExtend_ne (w : Width) (x y : BitVec w.bits) :
    (x.signExtend 64 != y.signExtend 64) = (x != y) := by
  simp only [bne, signExtend_inj]

theorem rep_bool_inj (b c : Bool) :
    ((if b then (1 : BitVec 64) else 0) == if c then 1 else 0) = (b == c) := by
  cases b <;> cases c <;> decide

theorem rep_bool_ne (b c : Bool) :
    ((if b then (1 : BitVec 64) else 0) != if c then 1 else 0) = (b != c) := by
  cases b <;> cases c <;> decide

/-! ## The families -/

section
variable {r0 r1 : BB}

theorem int2_sound {w : Width} {F : BitVec w.bits → BitVec w.bits → Val} {e : BB}
    (hF : ∀ x y, Agree r0 (x.signExtend 64) → Agree r1 (y.signExtend 64) → GamLo e (F x y)) :
    ∀ l : List Val, (∀ i (h : i < l.length), i < 2 → Gam (if i = 0 then r0 else r1) l[i]) →
      GamLo e (int2 w F l) := by
  intro l hl
  match l with
  | [a, b] =>
    cases ha : a.asInt w with
    | none => simp only [int2, ha]; exact .inl rfl
    | some x =>
      cases hb : b.asInt w with
      | none => simp only [int2, ha, hb]; exact .inl rfl
      | some y =>
        simp only [int2, ha, hb]
        have h0 := hl 0 (by simp) (by decide); have h1 := hl 1 (by simp) (by decide)
        simp only [ite_true, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
        rw [asInt_some ha] at h0; rw [asInt_some hb] at h1
        exact hF x y h0.int (by simpa using h1.int)
  | [] => exact .inl rfl
  | [_] => exact .inl rfl
  | _ :: _ :: _ :: _ => exact .inl rfl

theorem int1_sound {w : Width} {F : BitVec w.bits → Val} {e : BB}
    (hF : ∀ x, Agree r0 (x.signExtend 64) → GamLo e (F x)) :
    ∀ l : List Val, (∀ i (h : i < l.length), i < 2 → Gam (if i = 0 then r0 else r1) l[i]) →
      GamLo e (int1 w F l) := by
  intro l hl
  match l with
  | [a] =>
    cases ha : a.asInt w with
    | none => simp only [int1, ha]; exact .inl rfl
    | some x =>
      simp only [int1, ha]
      have h0 := hl 0 (by simp) (by decide)
      simp only [ite_true, List.getElem_cons_zero] at h0
      rw [asInt_some ha] at h0
      exact hF x h0.int
  | [] => exact .inl rfl
  | _ :: _ :: _ => exact .inl rfl

theorem bool2_sound {F : Bool → Bool → Bool} {e : BB}
    (hF : ∀ x y, Agree r0 (if x then 1 else 0) → Agree r1 (if y then 1 else 0) →
      GamLo e (.bool (F x y))) :
    ∀ l : List Val, (∀ i (h : i < l.length), i < 2 → Gam (if i = 0 then r0 else r1) l[i]) →
      GamLo e (bool2 F l) := by
  intro l hl
  match l with
  | [a, b] =>
    cases ha : a.asBool with
    | none => simp only [bool2, ha]; exact .inl rfl
    | some x =>
      cases hb : b.asBool with
      | none => simp only [bool2, ha, hb]; exact .inl rfl
      | some y =>
        simp only [bool2, ha, hb]
        have h0 := hl 0 (by simp) (by decide); have h1 := hl 1 (by simp) (by decide)
        simp only [ite_true, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
        rw [asBool_some ha] at h0; rw [asBool_some hb] at h1
        exact hF x y h0.bool (by simpa using h1.bool)
  | [] => exact .inl rfl
  | [_] => exact .inl rfl
  | _ :: _ :: _ :: _ => exact .inl rfl

end

theorem gamLo_int_of_agree {e : BB} {w : Width} {z : BitVec w.bits} (h : Agree e (z.signExtend 64)) :
    GamLo e (.int w z) := .inr (.inr (.inl ⟨w, z, rfl, h.lo _⟩))

theorem gamLo_bool_of_agree {e : BB} {b : Bool} (h : Agree e (if b then 1 else 0)) :
    GamLo e (.bool b) := .inr (.inr (.inr ⟨b, rfl, h.lo _⟩))


/-! ## Width conversions -/
theorem signExtend_signExtend_of_le {n n' : Nat} (x : BitVec n) (h1 : n ≤ n') (h2 : n' ≤ 64) :
    (x.signExtend n').signExtend 64 = x.signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_signExtend, BitVec.msb_signExtend]
  by_cases h3 : i < n' <;> by_cases h4 : i < n <;> simp [h3, h4, hi]
  · omega
  · by_cases h5 : n' ≤ n
    · have : n = n' := by omega
      subst this; simp only [BitVec.msb_eq_getMsbD_zero, Nat.le_refl, ite_true, Nat.sub_self]
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp [BitVec.getMsbD]
      · simp [hpos]
    · have : 0 < n' := by omega
      simp [h5, this]
theorem zext_rep {n n' : Nat} (x : BitVec n) (h1 : n < n') (h2 : n' ≤ 64) :
    (x.setWidth n').signExtend 64 = x.signExtend 64 &&& lowMask n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [lowMask, BitVec.getLsbD_signExtend, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, BitVec.getLsbD_setWidth, BitVec.msb_setWidth]
  by_cases h3 : i < n' <;> by_cases h4 : i < n <;> simp [h3, h4, hi]
  · have : i - n < 64 := by omega
    simp [this, BitVec.getLsbD_of_ge x i (by omega)]
  · omega
  · have : i - n < 64 := by omega
    simp [this, BitVec.getLsbD_of_ge x (n' - 1) (by omega)]

theorem ofInt_toInt64 (n : Nat) (h : n ≤ 64) (ai : Int64) :
    BitVec.ofInt n ai.toInt = ai.toBitVec.setWidth n := by
  rw [← BitVec.signExtend_eq_setWidth_of_le _ h, BitVec.signExtend]; rfl

theorem agree_zext {a ak X L : BitVec 64} (ha : Agree (a, ak) X) :
    Agree (a &&& L, ak ||| ~~~L) (X &&& L) := by
  simp only [Agree] at *; bv_decide

theorem agree_self (z k : BitVec 64) : Agree (z, k) z := by simp [Agree]

theorem cvt_rep (b : Bool) : ((if b then (1 : BitVec 8) else 0).signExtend 64) = if b then 1 else 0 := by
  cases b <;> decide

/-! ## Transfer functions of the non-shift families -/

/-- **Soundness of the non-shift transfer functions**: if the arguments have the bits their
entries claim, the result has (on its width's bits) the bits the transfer claims. -/
theorem tk_sound {k : KOp} (hk : ∀ s w a, k ≠ .shift s w a) (hv : validB k = true) (ai : Int64)
    {r0 r1 : BB} (m0 : Masked r0) (m1 : Masked r1) (l : List Val)
    (hl : ∀ i (h : i < l.length), i < 2 → Gam (if i = 0 then r0 else r1) l[i]) :
    GamLo (tk k ai r0 r1) (sem k ai l) := by
  obtain ⟨a, ak⟩ := r0
  obtain ⟨b, bk⟩ := r1
  cases k with
  | const w =>
    refine gamLo_int_of_agree ?_
    simp only [tk, sext]
    rw [ofInt_toInt64 _ (width_le w)]
    exact agree_self _ _
  | constBool =>
    refine gamLo_bool_of_agree ?_
    simp only [tk]
    exact agree_self _ _
  | and w =>
    exact int2_sound (fun x y hx hy => gamLo_int_of_agree (by
      rw [BitVec.signExtend_and]; exact agree_and hx hy m0 m1)) l hl
  | or w =>
    exact int2_sound (fun x y hx hy => gamLo_int_of_agree (by
      rw [BitVec.signExtend_or]; exact agree_or hx hy m0 m1)) l hl
  | xor w =>
    exact int2_sound (fun x y hx hy => gamLo_int_of_agree (by
      rw [BitVec.signExtend_xor]; exact agree_xor hx hy)) l hl
  | com w =>
    exact int1_sound (r1 := (b, bk)) (fun x hx => gamLo_int_of_agree (by
      rw [BitVec.signExtend_not (width_pos w)]; exact agree_not hx)) l hl
  | eq w =>
    exact int2_sound (fun x y hx hy => gamLo_bool_of_agree (by
      have := agree_eq hx hy; rwa [signExtend_inj] at this)) l hl
  | neq w =>
    exact int2_sound (fun x y hx hy => gamLo_bool_of_agree (by
      have := agree_neq hx hy
      rwa [signExtend_ne] at this)) l hl
  | eqB =>
    exact bool2_sound (fun x y hx hy => gamLo_bool_of_agree (by
      have := agree_eq hx hy; rwa [rep_bool_inj] at this)) l hl
  | neqB =>
    exact bool2_sound (fun x y hx hy => gamLo_bool_of_agree (by
      have := agree_neq hx hy; rwa [rep_bool_ne] at this)) l hl
  | signExt w w' =>
    have hle : w.bits ≤ w'.bits := by simp [validB] at hv; omega
    exact int1_sound (r1 := (b, bk)) (fun x hx => gamLo_int_of_agree (by
      rw [signExtend_signExtend_of_le x hle (width_le w')]; exact hx)) l hl
  | zeroExt w w' =>
    have hlt : w.bits < w'.bits := by simpa [validB] using hv
    exact int1_sound (r1 := (b, bk)) (fun x hx => gamLo_int_of_agree (by
      rw [zext_rep x hlt (width_le w')]; exact agree_zext hx)) l hl
  | trunc w w' =>
    have hlt : w'.bits < w.bits := by simpa [validB] using hv
    exact int1_sound (r1 := (b, bk)) (fun x hx => .inr (.inr (.inl ⟨w', _, rfl, by
      have h := hx.lo w'.bits
      simp only [AgreeLo, tk] at h ⊢
      rw [BitVec.setWidth_and, BitVec.setWidth_xor] at h ⊢
      rw [setWidth_signExtend_of_le (x.setWidth w'.bits) (Nat.le_refl _) (width_le w'),
        BitVec.setWidth_eq]
      rwa [setWidth_signExtend_of_le x (Nat.le_of_lt hlt) (width_le w)] at h⟩))) l hl
  | copy =>
    match l with
    | [x] => have h0 := hl 0 (by simp) (by decide); simpa [sem, tk] using h0.lo
    | [] => exact .inl rfl
    | _ :: _ :: _ => exact .inl rfl
  | cvt =>
    match l with
    | [x] =>
      have h0 := hl 0 (by simp) (by decide)
      simp only [ite_true, List.getElem_cons_zero] at h0
      simp only [sem, Conv.boolToUint8]
      cases hx : x.asBool with
      | none => exact .inl rfl
      | some c =>
        rw [asBool_some hx] at h0
        refine gamLo_int_of_agree ?_
        rw [cvt_rep]; exact h0.bool
    | [] => exact .inl rfl
    | _ :: _ :: _ => exact .inl rfl
  | not =>
    match l with
    | [x] =>
      have h0 := hl 0 (by simp) (by decide)
      simp only [ite_true, List.getElem_cons_zero] at h0
      simp only [sem, Cmp.not, bool1]
      cases hx : x.asBool with
      | none => exact .inl rfl
      | some c =>
        rw [asBool_some hx] at h0
        exact .inr (.inr (.inr ⟨_, rfl, agreeLo_not_bool c h0.bool⟩))
    | [] => exact .inl rfl
    | _ :: _ :: _ => exact .inl rfl
  | andB =>
    match l with
    | [x, y] =>
      have h0 := hl 0 (by simp) (by decide); have h1 := hl 1 (by simp) (by decide)
      simp only [ite_true, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
      simp only [Nat.one_ne_zero, ite_false] at h1
      simp only [sem, Cmp.andB, tk]
      cases hx : x.asBool with
      | none =>
        cases hy : y.asBool with
        | none => exact .inl rfl
        | some d =>
          cases d
          · rw [asBool_some hy] at h1
            exact .inr (.inr (.inr ⟨false, rfl, agreeLo_and_false_r h1.bool m1 m0⟩))
          · exact .inl rfl
      | some c =>
        rw [asBool_some hx] at h0
        cases c
        · exact .inr (.inr (.inr ⟨false, rfl, agreeLo_and_false_l h0.bool m1 m0⟩))
        · cases hy : y.asBool with
          | none => exact .inl rfl
          | some d =>
            rw [asBool_some hy] at h1
            cases d
            · exact .inr (.inr (.inr ⟨false, rfl, agreeLo_and_false_r h1.bool m1 m0⟩))
            · refine gamLo_bool_of_agree ?_
              have := agree_and h0.bool h1.bool m0 m1
              simpa using this
    | [] => exact .inl rfl
    | [_] => exact .inl rfl
    | _ :: _ :: _ :: _ => exact .inl rfl
  | orB =>
    match l with
    | [x, y] =>
      have h0 := hl 0 (by simp) (by decide); have h1 := hl 1 (by simp) (by decide)
      simp only [ite_true, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
      simp only [Nat.one_ne_zero, ite_false] at h1
      simp only [sem, Cmp.orB, tk]
      cases hx : x.asBool with
      | none =>
        cases hy : y.asBool with
        | none => exact .inl rfl
        | some d =>
          cases d
          · exact .inl rfl
          · rw [asBool_some hy] at h1
            exact .inr (.inr (.inr ⟨true, rfl, agreeLo_or_true_r h1.bool m1 m0⟩))
      | some c =>
        rw [asBool_some hx] at h0
        cases c
        · cases hy : y.asBool with
          | none => exact .inl rfl
          | some d =>
            rw [asBool_some hy] at h1
            cases d
            · refine gamLo_bool_of_agree ?_
              have := agree_or h0.bool h1.bool m0 m1
              simpa using this
            · exact .inr (.inr (.inr ⟨true, rfl, agreeLo_or_true_r h1.bool m1 m0⟩))
        · exact .inr (.inr (.inr ⟨true, rfl, agreeLo_or_true_l h0.bool m1 m0⟩))
    | [] => exact .inl rfl
    | [_] => exact .inl rfl
    | _ :: _ :: _ :: _ => exact .inl rfl
  | shift s w a => exact absurd rfl (hk s w a)

end GoFV.Proof.KnownBits
