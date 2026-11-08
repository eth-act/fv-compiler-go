import GoFV.Proof.Rules.Attr
import GoFV.Proof.Rules.Den
import GoFV.Proof.Retype
import GoFV.Proof.PtrAddr

variable [GoFV.SSA.Sem.Addrs]

/-!
# Lemmas of the rule-lemma tactics (`GoFV/Proof/Rules/Tactic.lean`)

Facts about the P1 semantics (`GoFV.SSA.Sem`) and the denotation (`GoFV/Proof/Rules/Den.lean`)
in the forms `rule_auto` needs, in the simp sets `rule_sem` and `rule_arith`
(`GoFV/Proof/Rules/Attr.lean`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-! ## Values -/


@[rule_sem] theorem val_asInt_int_ne {w w' : Width} (x : BitVec w.bits) (h : w ≠ w') :
    (Val.int w x).asInt w' = none := by
  simp [Val.asInt, h]

@[rule_sem] theorem val_asInt_bool (b : Bool) (w : Width) : (Val.bool b).asInt w = none := rfl
@[rule_sem] theorem val_asInt_poison (w : Width) : Val.poison.asInt w = none := rfl
@[rule_sem] theorem val_asInt_tuple (vs : List Val) (w : Width) : (Val.tuple vs).asInt w = none := rfl
@[rule_sem] theorem val_asInt_mem (m : Mem) (w : Width) : (Val.mem m).asInt w = none := rfl
@[rule_sem] theorem val_asBool_bool (b : Bool) : (Val.bool b).asBool = some b := rfl
@[rule_sem] theorem val_asBool_int (w : Width) (x : BitVec w.bits) : (Val.int w x).asBool = none := rfl
@[rule_sem] theorem val_asBool_poison : Val.poison.asBool = none := rfl
@[rule_sem] theorem val_asNat_int (w : Width) (x : BitVec w.bits) : (Val.int w x).asNat = some x.toNat :=
  rfl
@[rule_sem] theorem val_asNat_bool (b : Bool) : (Val.bool b).asNat = none := rfl
@[rule_sem] theorem val_asNat_poison : Val.poison.asNat = none := rfl

theorem val_asInt_eq_some {v : Val} {w : Width} {x : BitVec w.bits} :
    v.asInt w = some x ↔ v = .int w x := by
  constructor
  · intro h
    cases v with
    | int w' y =>
      simp only [Val.asInt] at h
      split at h
      · subst_vars; cases h; rfl
      · cases h
    | _ => cases h
  · rintro rfl; simp

theorem val_asBool_eq_some {v : Val} {b : Bool} : v.asBool = some b ↔ v = .bool b := by
  cases v <;> simp [Val.asBool] <;> intro h <;> cases h

/-- A rotation amount is an integer of some width or no amount. -/
theorem val_asNat_cases (v : Val) : v.asNat = none ∨ ∃ w x, v = .int w x := by
  cases v with
  | int w x => exact Or.inr ⟨w, x, rfl⟩
  | _ => exact Or.inl rfl

/-- A value of shape `Ty.int w` that is not a `w`-bit integer is `poison` or, at 64 bits, a
pointer without a concrete address (a global held in a `uintptr`, `Val.hasTy`). -/
theorem val_poison_of_asInt_none {v : Val} {w : Width} (h : v.asInt w = none)
    (ht : v.hasTy (.int w) = true) : v = .poison ∨ (w = .w64 ∧ ∃ p, v = .ptr p) := by
  cases v with
  | poison => exact .inl rfl
  | int w' x =>
    simp only [Val.hasTy, beq_iff_eq] at ht
    subst ht; simp at h
  | ptr p => cases w <;> simp_all [Val.hasTy]
  | _ => simp [Val.hasTy] at ht

/-- An integer of width `w` read back at `w` through a retype to `t` fails: `t` is an integer
shape of another width (narrower: the low bits; wider: `poison`), a pointer shape for `w ≠ 64`
(a 64-bit integer keeps its word there), or another shape (`poison`; `Val.retype`). -/
def tyOtherInt (t : Ty) (w : Width) : Bool :=
  match t with
  | .int w' => w' != w
  | .ptr _ => w != .w64
  | _ => true

@[rule_sem] theorem tyOtherInt_int (w w' : Width) : tyOtherInt (Ty.int w') w = (w' != w) := rfl
@[rule_sem] theorem tyOtherInt_bool (w : Width) : tyOtherInt Ty.bool w = true := rfl
@[rule_sem] theorem tyOtherInt_ptr (w : Width) (e : Option Nat) :
    tyOtherInt (Ty.ptr e) w = (w != .w64) := rfl

/-- Below 64 bits only the integer shape of the width keeps an integer (as on pointer-free
shapes before §3.3's pointer words): the rule tactics get the type itself. -/
@[rule_sem] theorem tyOtherInt_w8_eq_false (t : Ty) : tyOtherInt t .w8 = false ↔ t = .int .w8 := by
  cases t with
  | int w => cases w <;> simp [tyOtherInt]
  | _ => simp [tyOtherInt]

@[rule_sem] theorem tyOtherInt_w16_eq_false (t : Ty) :
    tyOtherInt t .w16 = false ↔ t = .int .w16 := by
  cases t with
  | int w => cases w <;> simp [tyOtherInt]
  | _ => simp [tyOtherInt]

@[rule_sem] theorem tyOtherInt_w32_eq_false (t : Ty) :
    tyOtherInt t .w32 = false ↔ t = .int .w32 := by
  cases t with
  | int w => cases w <;> simp [tyOtherInt]
  | _ => simp [tyOtherInt]

/-- At 64 bits an integer keeps its word at its integer shape and at every pointer shape
(`rule_split_ptr_or` splits on it where a condition reads the type). -/
theorem tyOtherInt_w64_eq_false (t : Ty) :
    tyOtherInt t .w64 = false ↔ t = .int .w64 ∨ ∃ el, t = .ptr el := by
  cases t with
  | int w => cases w <;> simp [tyOtherInt]
  | _ => simp [tyOtherInt]

@[rule_sem] theorem retype_int_same (w : Width) (x : BitVec w.bits) :
    (Val.int w x).retype (.int w) = .int w x := by
  simp [Val.retype, BitVec.setWidth_eq]

/-- `t` is the `bool` shape (a `Bool` test the rule tactic splits on). -/
def tyIsBool : Ty → Bool
  | .bool => true
  | _ => false

@[rule_sem] theorem tyIsBool_bool : tyIsBool .bool = true := rfl
@[rule_sem] theorem tyIsBool_int (w : Width) : tyIsBool (.int w) = false := rfl
@[rule_sem] theorem tyIsBool_ptr (e : Option Nat) : tyIsBool (.ptr e) = false := rfl

theorem tyIsBool_eq {t : Ty} (h : tyIsBool t = true) : t = .bool := by
  cases t <;> first | rfl | cases h

@[rule_sem] theorem retype_bool (t : Ty) (b : Bool) :
    (Val.bool b).retype t = if tyIsBool t then .bool b else .poison := by
  cases t <;> rfl

@[rule_sem] theorem retype_poison (t : Ty) : Val.poison.retype t = .poison := by
  cases t <;> rfl

@[rule_sem] theorem retype_tuple (t : Ty) (vs : List Val) :
    (Val.tuple vs).retype t = match t with
      | .tuple ts => (Val.retypePre ts vs).elim .poison .tuple
      | _ => .poison := by
  cases t with
  | tuple ts => unfold Val.retype; cases h : Val.retypePre ts vs <;> simp [h]
  | _ => rfl

@[rule_sem] theorem retype_bool_ty (v : Val) :
    v.retype .bool = match v with | .bool b => .bool b | _ => .poison := by
  cases v <;> rfl

/-- An integer read at its own width through a retype: unchanged unless `tyOtherInt`. -/
@[rule_sem] theorem asInt_retype_int (t : Ty) (w : Width) (x : BitVec w.bits) :
    ((Val.int w x).retype t).asInt w = if tyOtherInt t w then none else some x := by
  cases t with
  | int w' =>
    simp only [Val.retype, GoFV.Proof.Rules.tyOtherInt]
    by_cases h : w' = w
    · subst h; simp [BitVec.setWidth_eq]
    · have : (w' != w) = true := by simpa using h
      simp only [this, ite_true]
      split
      · exact val_asInt_int_ne _ h
      · rfl
  | ptr e => cases w <;> rfl
  | _ => cases w <;> rfl

@[rule_sem] theorem asBool_retype (t : Ty) (v : Val) :
    (v.retype t).asBool = if tyIsBool t then v.asBool else none := by
  have hb := Val.retype_hasTy t v
  cases t with
  | bool => cases v <;> rfl
  | _ =>
    simp only [tyIsBool, Bool.false_eq_true, ite_false]
    generalize Val.retype _ v = r at hb ⊢
    cases r <;> simp_all [Val.hasTy, Val.asBool]

/-- An integer has its own integer shape; a 64-bit integer also every pointer shape (a pointer
word holding a concrete address, §3.3): exactly the shapes at which it reads back as itself. -/
@[rule_sem] theorem hasTy_int (w : Width) (x : BitVec w.bits) (t : Ty) :
    (Val.int w x).hasTy t = true ↔ tyOtherInt t w = false := by
  cases t with
  | int w' => simp only [Val.hasTy, tyOtherInt, bne_eq_false_iff_eq]; exact ⟨fun h => (beq_iff_eq.1 h).symm, fun h => beq_iff_eq.2 h.symm⟩
  | ptr e => cases w <;> simp [Val.hasTy, tyOtherInt]
  | _ => simp [Val.hasTy, tyOtherInt]

/-- A 64-bit integer keeps its word at a pointer shape. -/
@[rule_sem] theorem retype_int64_of_isPtrTy {t : Ty} (h : isPtrTy t = true) (x : BitVec 64) :
    (Val.int .w64 x).retype t = .int .w64 x := by
  cases t <;> first | rfl | cases h

@[rule_sem] theorem tyOtherInt_of_isPtrTy {t : Ty} (h : isPtrTy t = true) :
    tyOtherInt t .w64 = false := by
  cases t <;> first | rfl | cases h

@[rule_sem] theorem hasTy_bool (b : Bool) (t : Ty) : (Val.bool b).hasTy t = true ↔ t = .bool := by
  cases t <;> simp [Val.hasTy]

@[rule_sem] theorem hasTy_poison (t : Ty) : Val.poison.hasTy t = true := rfl

/-! ## Refinement -/

@[rule_sem] theorem refines_poison (v : Val) : Refines .poison v := .poison v

@[rule_sem] theorem refines_int_int (w : Width) (x y : BitVec w.bits) :
    Refines (.int w x) (.int w y) ↔ x = y := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .int w x

@[rule_sem] theorem refines_bool_bool (a b : Bool) : Refines (.bool a) (.bool b) ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .bool a

@[rule_sem] theorem refines_int_poison (w : Width) (x : BitVec w.bits) :
    Refines (.int w x) .poison ↔ False := by
  constructor
  · intro h; cases h
  · intro h; cases h

@[rule_sem] theorem refines_bool_poison (b : Bool) : Refines (.bool b) .poison ↔ False := by
  constructor
  · intro h; cases h
  · intro h; cases h

theorem refines_of_eq {a b : Val} (h : a = b) : Refines a b := h ▸ Refines.refl a

@[rule_sem] theorem refines_tuple_tuple (as bs : List Val) :
    Refines (.tuple as) (.tuple bs) ↔ RefinesList as bs := by
  constructor
  · intro h; cases h; assumption
  · intro h; exact .tuple h

@[rule_sem] theorem refinesList_nil : RefinesList [] [] := .nil

@[rule_sem] theorem refinesList_cons (a b : Val) (as bs : List Val) :
    RefinesList (a :: as) (b :: bs) ↔ Refines a b ∧ RefinesList as bs := by
  constructor
  · intro h; cases h; exact ⟨by assumption, by assumption⟩
  · rintro ⟨h1, h2⟩; exact .cons h1 h2

/-! ## Integer arithmetic of auxints -/

theorem wrapInt_true (w : Nat) (x : Int) : wrapInt w true x = x.bmod (2 ^ w) := rfl
theorem wrapInt_false (w : Nat) (x : Int) : wrapInt w false x = x.emod (2 ^ w) := rfl

theorem ofInt_bmod_of_le {w k : Nat} (h : w ≤ k) (x : Int) :
    BitVec.ofInt w (x.bmod (2 ^ k)) = BitVec.ofInt w x := by
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_ofInt]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 h)

theorem ofInt_emod_of_le {w k : Nat} (h : w ≤ k) (x : Int) :
    BitVec.ofInt w (x.emod (2 ^ k)) = BitVec.ofInt w x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  congr 1
  have : ((2 : Int) ^ w) ∣ 2 ^ k := by
    have h' := Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h)
    simpa using h'
  exact Int.emod_emod_of_dvd x this

@[rule_sem] theorem const_w8 (a : Int64) : Conv.const .w8 a = .i8 (BitVec.ofInt 8 (wrapInt 8 true a.toInt)) := by
  simp only [GoFV.SSA.Sem.Conv.const, GoFV.Proof.Rules.wrapInt_true, GoFV.SSA.Sem.Width.bits]
  rw [ofInt_bmod_of_le (Nat.le_refl 8)]
@[rule_sem] theorem const_w16 (a : Int64) :
    Conv.const .w16 a = .i16 (BitVec.ofInt 16 (wrapInt 16 true a.toInt)) := by
  simp only [GoFV.SSA.Sem.Conv.const, GoFV.Proof.Rules.wrapInt_true, GoFV.SSA.Sem.Width.bits]
  rw [ofInt_bmod_of_le (Nat.le_refl 16)]
@[rule_sem] theorem const_w32 (a : Int64) :
    Conv.const .w32 a = .i32 (BitVec.ofInt 32 (wrapInt 32 true a.toInt)) := by
  simp only [GoFV.SSA.Sem.Conv.const, GoFV.Proof.Rules.wrapInt_true, GoFV.SSA.Sem.Width.bits]
  rw [ofInt_bmod_of_le (Nat.le_refl 32)]
@[rule_sem] theorem const_w64 (a : Int64) : Conv.const .w64 a = .i64 (BitVec.ofInt 64 a.toInt) := rfl

@[rule_arith] theorem ofInt_wrapInt_true {w k : Nat} (h : w ≤ k) (x : Int) :
    BitVec.ofInt w (wrapInt k true x) = BitVec.ofInt w x := ofInt_bmod_of_le h x

@[rule_arith] theorem ofInt_wrapInt_false {w k : Nat} (h : w ≤ k) (x : Int) :
    BitVec.ofInt w (wrapInt k false x) = BitVec.ofInt w x := ofInt_emod_of_le h x

@[rule_sem, rule_arith] theorem ofInt_int64_ofInt {w : Nat} (h : w ≤ 64) (x : Int) :
    BitVec.ofInt w (Int64.ofInt x).toInt = BitVec.ofInt w x := by
  rw [Int64.toInt_ofInt]
  exact ofInt_bmod_of_le h x

/-- Range of a signed auxint of width `w` (`w` = 8, 16, 32 in practice). -/
theorem wrapInt_true_range (w : Nat) (x : Int) :
    -(((2 ^ w : Nat) : Int) / 2) ≤ wrapInt w true x ∧ wrapInt w true x < (((2 ^ w : Nat) : Int) + 1) / 2 :=
  ⟨Int.le_bmod (Nat.pos_of_ne_zero (by simp)), Int.bmod_lt (Nat.pos_of_ne_zero (by simp))⟩

theorem wrapInt_false_range (w : Nat) (x : Int) :
    0 ≤ wrapInt w false x ∧ wrapInt w false x < 2 ^ w := by
  rw [wrapInt_false]
  have : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ this⟩

theorem int64_toInt_range (a : Int64) : -(2 ^ 63 : Int) ≤ a.toInt ∧ a.toInt < 2 ^ 63 :=
  ⟨Int64.le_toInt a, Int64.toInt_lt a⟩

@[rule_arith] theorem ofInt_sub' (w : Nat) (x y : Int) :
    BitVec.ofInt w (x - y) = BitVec.ofInt w x - BitVec.ofInt w y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-! ## Ring forms for `grind` (`rule_close`): complement and constant shifts as ring terms -/

theorem bv_not_eq {w : Nat} (x : BitVec w) : ~~~x = -x - 1 := by
  rw [BitVec.neg_eq_not_add]; exact (BitVec.add_sub_cancel _ _).symm

theorem bv_shl_nat {w : Nat} (x : BitVec w) (n : Nat) : x <<< n = x * (2 ^ n : Nat) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_twoPow]

/-! ## Shifts and rotations by `Nat` amounts (`rule_sem`)

The families cap a shift amount at the width (`min s.toNat w`), which changes no result. -/

@[rule_sem] theorem shiftLeft_min {w : Nat} (x : BitVec w) (n : Nat) : x <<< min n w = x <<< n := by
  by_cases h : n ≤ w
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), BitVec.shiftLeft_eq_zero (Nat.le_refl w),
      BitVec.shiftLeft_eq_zero (by omega)]

@[rule_sem] theorem ushiftRight_min {w : Nat} (x : BitVec w) (n : Nat) : x >>> min n w = x >>> n := by
  by_cases h : n ≤ w
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), BitVec.ushiftRight_eq_zero (Nat.le_refl w),
      BitVec.ushiftRight_eq_zero (by omega)]

@[rule_sem] theorem sshiftRight_min {w : Nat} (x : BitVec w) (n : Nat) :
    x.sshiftRight (min n w) = x.sshiftRight n := by
  by_cases h : n ≤ w
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega)]
    ext i hi
    simp only [BitVec.getElem_sshiftRight]
    have h1 : ¬ (w + i < w) := by omega
    have h2 : ¬ (n + i < w) := by omega
    simp [h1, h2]

/-! ## Rotations as sums of disjoint shifts (`rule_close`) -/

theorem shl_ushr_disj {w : Nat} (x : BitVec w) (a b : Nat) (hab : a + b = w) :
    x <<< a &&& x >>> b = 0 := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight]
  by_cases h : i < a
  · simp [h]
  · simp only [h, decide_false, Bool.not_false, Bool.true_and]
    simp [BitVec.getLsbD_of_ge x (b + i) (by omega)]

theorem xor_eq_or_of_and_eq_zero {w : Nat} {x y : BitVec w} (h : x &&& y = 0) :
    x ^^^ y = x ||| y := by
  ext i hi
  have := congrArg (·[i]) h
  simp only [BitVec.getElem_and] at this
  simp only [BitVec.getElem_xor, BitVec.getElem_or]
  revert this; cases x[i] <;> cases y[i] <;> simp

theorem rot_or {w : Nat} (x : BitVec w) (a b : Nat) (ha : a ≤ w) (hab : a + b = w) :
    x <<< a ||| x >>> b = x.rotateLeft a := by
  rcases Nat.lt_or_eq_of_le ha with h | h
  · rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt h]; congr 2; omega
  · subst h; have hb : b = 0 := by omega
    subst hb; simp [BitVec.rotateLeft_def, BitVec.shiftLeft_eq_zero, BitVec.ushiftRight_eq_zero]

theorem rot_add {w : Nat} (x : BitVec w) (a b : Nat) (ha : a ≤ w) (hab : a + b = w) :
    x <<< a + x >>> b = x.rotateLeft a := by
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ (shl_ushr_disj x a b hab), rot_or x a b ha hab]

theorem rot_xor {w : Nat} (x : BitVec w) (a b : Nat) (ha : a ≤ w) (hab : a + b = w) :
    x <<< a ^^^ x >>> b = x.rotateLeft a := by
  rw [xor_eq_or_of_and_eq_zero (shl_ushr_disj x a b hab), rot_or x a b ha hab]

theorem rot_add' {w : Nat} (x : BitVec w) (a b : Nat) (ha : a ≤ w) (hab : a + b = w) :
    x >>> b + x <<< a = x.rotateLeft a := by
  rw [BitVec.add_comm, rot_add x a b ha hab]

theorem rot_or' {w : Nat} (x : BitVec w) (a b : Nat) (ha : a ≤ w) (hab : a + b = w) :
    x >>> b ||| x <<< a = x.rotateLeft a := by
  rw [BitVec.or_comm, rot_or x a b ha hab]

theorem rot_xor' {w : Nat} (x : BitVec w) (a b : Nat) (ha : a ≤ w) (hab : a + b = w) :
    x >>> b ^^^ x <<< a = x.rotateLeft a := by
  rw [BitVec.xor_comm, rot_xor x a b ha hab]

theorem rotateLeft_congr {w : Nat} (x : BitVec w) {a b : Nat} (h : a % w = b % w) :
    x.rotateLeft a = x.rotateLeft b := by
  simp only [BitVec.rotateLeft_def, h]

/-! ### Rotations by a variable amount `y` and `w - y` (`Sub` of a width constant)

The rotate rules shift by `y` and by `(Const [w]) - y` at the amount's width `v`; one of the
shifts is bounded, so `y ≤ w` (`rule_rot`). -/

theorem toNat_ofNat_sub {w v : Nat} (y : BitVec v) (hw : w < 2 ^ v) (h : y.toNat ≤ w) :
    (BitVec.ofNat v w - y).toNat = w - y.toNat := by
  rw [BitVec.toNat_sub_of_le] <;> simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  exact h

theorem rot_add_sub {w v : Nat} (x : BitVec w) (y : BitVec v) (hw : w < 2 ^ v) (h : y.toNat ≤ w) :
    x <<< y.toNat + x >>> (BitVec.ofNat v w - y).toNat = x.rotateLeft y.toNat := by
  rw [toNat_ofNat_sub y hw h]; exact rot_add x _ _ h (by omega)

theorem rot_or_sub {w v : Nat} (x : BitVec w) (y : BitVec v) (hw : w < 2 ^ v) (h : y.toNat ≤ w) :
    x <<< y.toNat ||| x >>> (BitVec.ofNat v w - y).toNat = x.rotateLeft y.toNat := by
  rw [toNat_ofNat_sub y hw h]; exact rot_or x _ _ h (by omega)

theorem rot_xor_sub {w v : Nat} (x : BitVec w) (y : BitVec v) (hw : w < 2 ^ v) (h : y.toNat ≤ w) :
    x <<< y.toNat ^^^ x >>> (BitVec.ofNat v w - y).toNat = x.rotateLeft y.toNat := by
  rw [toNat_ofNat_sub y hw h]; exact rot_xor x _ _ h (by omega)

theorem rot_add_sub' {w v : Nat} (x : BitVec w) (y : BitVec v) (hw : w < 2 ^ v) (h : y.toNat ≤ w) :
    x >>> y.toNat + x <<< (BitVec.ofNat v w - y).toNat =
      x.rotateLeft (BitVec.ofNat v w - y).toNat := by
  rw [toNat_ofNat_sub y hw h]; exact rot_add' x _ _ (by omega) (by omega)

theorem rot_or_sub' {w v : Nat} (x : BitVec w) (y : BitVec v) (hw : w < 2 ^ v) (h : y.toNat ≤ w) :
    x >>> y.toNat ||| x <<< (BitVec.ofNat v w - y).toNat =
      x.rotateLeft (BitVec.ofNat v w - y).toNat := by
  rw [toNat_ofNat_sub y hw h]; exact rot_or' x _ _ (by omega) (by omega)

theorem rot_xor_sub' {w v : Nat} (x : BitVec w) (y : BitVec v) (hw : w < 2 ^ v) (h : y.toNat ≤ w) :
    x >>> y.toNat ^^^ x <<< (BitVec.ofNat v w - y).toNat =
      x.rotateLeft (BitVec.ofNat v w - y).toNat := by
  rw [toNat_ofNat_sub y hw h]; exact rot_xor' x _ _ (by omega) (by omega)

/-! ## Rotation amounts (`rule_rotamt`)

`RotateLeft` reads its amount as a natural number of any integer width (`Val.asNat`), so the
amount of a pattern is a retyped node value; a rotation depends only on its amount modulo the
width, and every integer width is a multiple of every rotation width. The rotate-amount rules
(`x (And y c)`, `x (Add y c)`, `(Sub c y)`, nested rotations, …) then hold modulo the width:
`rule_rotamt` turns the amounts and the condition into `Nat`/`Int` arithmetic with remainders by
constants and adds the facts `omega` needs about the remaining atoms (`&&&`, `Int.tmod`). -/

/-- Whether a `w`-bit integer retyped to `t` is no longer an integer amount: a wider integer
shape or a `bool` shape (`poison`), or a pointer shape unless `w = 64` (`Val.retype`). -/
def retypeNone (t : Ty) (w : Width) : Bool :=
  match t with
  | .int w' => decide (w.bits < w'.bits)
  | .ptr _ => w != .w64
  | _ => true

@[rule_sem] theorem retypeNone_int (w w' : Width) :
    retypeNone (.int w') w = decide (w.bits < w'.bits) := rfl
@[rule_sem] theorem retypeNone_bool (w : Width) : retypeNone .bool w = true := rfl
@[rule_sem] theorem retypeNone_ptr (e : Option Nat) (w : Width) :
    retypeNone (.ptr e) w = (w != .w64) := rfl

/-- A retype that keeps a `w`-bit integer an integer of width `w` keeps it an amount. -/
@[rule_sem] theorem retypeNone_of_tyOtherInt {t : Ty} {w : Width} (h : tyOtherInt t w = false) :
    retypeNone t w = false := by
  cases t with
  | int w' =>
    simp only [tyOtherInt, bne_eq_false_iff_eq] at h
    subst h; simp [retypeNone]
  | ptr e => simpa [tyOtherInt, retypeNone] using h
  | _ => simp [tyOtherInt] at h

theorem rotateLeft_mod_pow {W : Width} (y : BitVec W.bits) (n b : Nat) (hb : 8 ≤ b) :
    y.rotateLeft (n % 2 ^ b) = y.rotateLeft n := by
  apply rotateLeft_congr
  have h8 : W.bits ∣ 2 ^ 8 := by cases W <;> decide
  exact Nat.mod_mod_of_dvd n (Nat.dvd_trans h8 (Nat.pow_dvd_pow 2 hb))

/-- A rotation by a retyped integer amount: `poison` where the retype is not an integer,
else the rotation by the integer (a narrower retype keeps the low bits, which a rotation of
at most 64 bits does not read beyond). -/
@[rule_sem] theorem rotate_retype_amt (t : Ty) (w W : Width) (x : BitVec w.bits)
    (y : BitVec W.bits) :
    ((Val.int w x).retype t).asNat.elim Val.poison (fun n => Val.int W (y.rotateLeft n)) =
      if retypeNone t w then Val.poison else Val.int W (y.rotateLeft x.toNat) := by
  cases t with
  | int w' =>
    simp only [Val.retype, retypeNone]
    by_cases h : w'.bits ≤ w.bits
    · have h' : ¬ w.bits < w'.bits := by omega
      simp only [h, h', ite_true, decide_false, Bool.false_eq_true, ite_false, Val.asNat,
        Option.elim_some, BitVec.toNat_setWidth]
      rw [rotateLeft_mod_pow y x.toNat w'.bits (by cases w' <;> decide)]
    · have h' : w.bits < w'.bits := by omega
      simp [h, h', Val.asNat]
  | ptr e =>
    cases w <;> simp [Val.retype, retypeNone, Val.asNat]
  | _ => cases w <;> simp [Val.retype, retypeNone, Val.asNat]

theorem rotateLeft_rotateLeft {w : Nat} (x : BitVec w) (a b : Nat) :
    (x.rotateLeft a).rotateLeft b = x.rotateLeft (a + b) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact Subsingleton.elim _ _
  have ha := Nat.mod_lt a hw
  have hb := Nat.mod_lt b hw
  have hab : (a % w + b % w < w ∧ (a + b) % w = a % w + b % w) ∨
      (w ≤ a % w + b % w ∧ (a + b) % w = a % w + b % w - w) := by
    rw [Nat.add_mod]
    rcases Nat.lt_or_ge (a % w + b % w) w with h | h
    · left; exact ⟨h, Nat.mod_eq_of_lt h⟩
    · right; exact ⟨h, by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]⟩
  have hc := Nat.mod_lt (a + b) hw
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft]
  generalize a % w = a' at *
  generalize b % w = b' at *
  generalize (a + b) % w = c at *
  by_cases h1 : i < b' <;> by_cases h2 : i < c <;> by_cases h3 : w - b' + i < a' <;>
    by_cases h4 : i - b' < a' <;>
    simp (disch := omega) only [h1, h2, h3, h4, ite_true, ite_false, decide_eq_true,
      Bool.true_and] <;>
    congr 1 <;> omega

@[rule_amt] theorem wrapInt8_omega (x : Int) : wrapInt 8 true x = (x + 128) % 256 - 128 := by
  rw [wrapInt_true, Int.bmod_def]; split <;> omega
@[rule_amt] theorem wrapInt16_omega (x : Int) :
    wrapInt 16 true x = (x + 32768) % 65536 - 32768 := by
  rw [wrapInt_true, Int.bmod_def]; split <;> omega
@[rule_amt] theorem wrapInt32_omega (x : Int) :
    wrapInt 32 true x = (x + 2147483648) % 4294967296 - 2147483648 := by
  rw [wrapInt_true, Int.bmod_def]; split <;> omega
@[rule_amt] theorem wrapInt64_omega (x : Int) :
    wrapInt 64 true x = (x + 9223372036854775808) % 18446744073709551616 - 9223372036854775808 := by
  rw [wrapInt_true, Int.bmod_def]; split <;> omega

@[rule_amt] theorem wrapInt_false_omega (w : Nat) (x : Int) : wrapInt w false x = x % 2 ^ w := rfl

@[rule_amt] theorem pat64_omega (a : Int) : pat64 a = (a % 2 ^ 64).toNat := rfl

/-! What `omega` needs about `a &&& b` (`rule_omega_facts`): its bounds, and its remainder by
`m = 2 ^ k` when one side's low `k` bits are all ones or all zeros. -/

theorem nat_and_le (a b : Nat) : a &&& b ≤ a ∧ a &&& b ≤ b := ⟨Nat.and_le_left, Nat.and_le_right⟩

theorem nat_and_ones_r (a b m k : Nat) (hm : m = 2 ^ k) (h : b % m = m - 1) :
    (a &&& b) % m = a % m := by
  subst hm; rw [Nat.and_mod_two_pow, h, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

theorem nat_and_ones_l (a b m k : Nat) (hm : m = 2 ^ k) (h : a % m = m - 1) :
    (a &&& b) % m = b % m := by
  rw [Nat.and_comm]; exact nat_and_ones_r b a m k hm h

theorem nat_and_zero_r (a b m k : Nat) (hm : m = 2 ^ k) (h : b % m = 0) :
    (a &&& b) % m = 0 := by
  subst hm; rw [Nat.and_mod_two_pow, h, Nat.and_zero]

theorem nat_and_zero_l (a b m k : Nat) (hm : m = 2 ^ k) (h : a % m = 0) :
    (a &&& b) % m = 0 := by
  rw [Nat.and_comm]; exact nat_and_zero_r b a m k hm h

/-- `Int.tmod` (Go's `%`) by its sign cases, for `omega`. -/
theorem tmod_facts (a b : Int) :
    (0 ≤ a → a.tmod b = a % b) ∧ (a < 0 → a.tmod b = -((-a) % b)) := by
  refine ⟨Int.tmod_eq_emod_of_nonneg, fun h => ?_⟩
  rw [← Int.tmod_eq_emod_of_nonneg (by omega), Int.neg_tmod, Int.neg_neg]

attribute [rule_amt] BitVec.toNat_and BitVec.toNat_or BitVec.toNat_add BitVec.toNat_sub
  BitVec.toNat_neg BitVec.toNat_ofInt BitVec.toNat_ofNat BitVec.toNat_setWidth Width.bits
  GoFV.Rules.bitwise GoFV.Rules.goRem GoFV.Rules.goQuo Option.getD_some Nat.reducePow
  Int.reducePow Int.reduceMod Int.reduceToNat Int.reduceNeg Nat.reduceMod Nat.reduceAnd
  Int.natCast_emod Int.natCast_pow

theorem rotateLeft_eq_self {w : Nat} (x : BitVec w) {a : Nat} (h : a % w = 0) :
    x.rotateLeft a = x := by
  rw [rotateLeft_congr x (b := 0) (by simpa using h)]
  simp [BitVec.rotateLeft_def, BitVec.shiftLeft_zero, BitVec.ushiftRight_eq_zero]

theorem rotateLeft_rotateLeft_congr {w : Nat} (x : BitVec w) {a b c : Nat}
    (h : (a + b) % w = c % w) : (x.rotateLeft a).rotateLeft b = x.rotateLeft c := by
  rw [rotateLeft_rotateLeft]; exact rotateLeft_congr x h

/-! ## Constant shifts (`rule_shamt`)

Go's `<<`/`>>` on auxints (`goShl`, `goShr`) as `BitVec` shifts: a constant-folded shift is the
shift of the constant. -/

@[rule_arith] theorem ofInt_goShl {w k : Nat} (h : w ≤ k) (x : Int) (s : Nat) :
    BitVec.ofInt w (goShl x s k) = BitVec.ofInt w x <<< s := by
  unfold goShl
  split
  · rw [BitVec.shiftLeft_eq_zero (by omega)]; rfl
  · rw [bv_shl_nat, BitVec.ofInt_mul]
    rw [show ((2 : Int) ^ s) = ((2 ^ s : Nat) : Int) by simp, BitVec.ofInt_natCast]; rfl

@[rule_arith] theorem ofInt_goShr_unsigned (w : Nat) (x : Int) (s : Nat) :
    BitVec.ofInt w (goShr (wrapInt w false x) s) = BitVec.ofInt w x >>> s := by
  unfold goShr
  rw [wrapInt_false, Int.shiftRight_eq_div_pow]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hpw : (2 : Int) ^ w ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide))
  obtain ⟨n, hn⟩ : ∃ n : Nat, x.emod (2 ^ w) = n :=
    ⟨_, (Int.toNat_of_nonneg (Int.emod_nonneg x hpw)).symm⟩
  have hlt : n < 2 ^ w := by
    have := Int.emod_lt_of_pos x (show (0 : Int) < 2 ^ w from Int.pow_pos (by decide))
    rw [show x % 2 ^ w = x.emod (2 ^ w) from rfl, hn] at this; exact_mod_cast this
  have hx : x % ((2 ^ w : Nat) : Int) = n := by rw [← hn]; simp; rfl
  rw [hn, hx, ← Int.natCast_ediv,
    ← Int.natCast_emod, Int.toNat_natCast, Int.toNat_natCast,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt)]

theorem ofInt_goShr_nonneg {w : Nat} (x : Int) (s : Nat) (h0 : 0 ≤ x) (h1 : x < 2 ^ w) :
    BitVec.ofInt w (goShr x s) = BitVec.ofInt w x >>> s := by
  have : wrapInt w false x = x := by rw [wrapInt_false]; exact Int.emod_eq_of_lt h0 h1
  rw [← ofInt_goShr_unsigned, this]

theorem ofInt_goShr_signed {w : Nat} (x : Int) (s : Nat) (h1 : -(((2 ^ w : Nat) : Int) / 2) ≤ x)
    (h2 : x < (((2 ^ w : Nat) : Int) + 1) / 2) :
    BitVec.ofInt w (goShr x s) = (BitVec.ofInt w x).sshiftRight s := by
  unfold goShr
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, BitVec.toInt_ofInt, BitVec.toInt_ofInt,
    Int.bmod_eq_of_le h1 h2]
  apply Int.bmod_eq_of_le
  · rcases Int.le_total x 0 with hx | hx
    · have := Int.le_shiftRight_of_nonpos (s := s) hx; omega
    · have := Int.le_shiftRight_of_nonneg (s := s) hx; omega
  · rcases Int.le_total x 0 with hx | hx
    · have := Int.shiftRight_le_of_nonpos (s := s) hx; omega
    · have := Int.shiftRight_le_of_nonneg (s := s) hx; omega

theorem shl_shl {w : Nat} (x : BitVec w) (a b c : Nat) (h : a + b = c) :
    x <<< a <<< b = x <<< c := by rw [← h, BitVec.shiftLeft_add]

theorem ushr_ushr {w : Nat} (x : BitVec w) (a b c : Nat) (h : a + b = c) :
    x >>> a >>> b = x >>> c := by rw [← h, BitVec.shiftRight_add]

theorem sshr_sshr {w : Nat} (x : BitVec w) (a b c : Nat) (h : a + b = c) :
    (x.sshiftRight a).sshiftRight b = x.sshiftRight c := by rw [← h, BitVec.sshiftRight_add]

theorem ushr_shl {w : Nat} (x : BitVec w) (n : Nat) : x >>> n <<< n = x &&& BitVec.allOnes w <<< n := by
  ext i hi
  by_cases h : i < n
  · simp [h]
  · simp [h, Nat.add_sub_of_le (Nat.le_of_not_lt h), hi]
theorem sshr_shl {w : Nat} (x : BitVec w) (n : Nat) : (x.sshiftRight n) <<< n = x &&& BitVec.allOnes w <<< n := by
  ext i hi
  by_cases h : i < n
  · simp [h]
  · simp only [BitVec.getElem_shiftLeft, BitVec.getElem_and, h, BitVec.getElem_allOnes,
      decide_false, Bool.not_false, Bool.true_and, Bool.and_true]
    rw [BitVec.getElem_sshiftRight]
    simp [show n + (i - n) = i by omega, hi]
theorem shl_ushr {w : Nat} (x : BitVec w) (n : Nat) : x <<< n >>> n = x &&& BitVec.allOnes w >>> n := by
  ext i hi
  by_cases h : n + i < w
  · simp [h]
  · simp [h]

theorem shl_ushr_shl {w : Nat} (x : BitVec w) (a b c d : Nat) (h1 : b ≤ a) (h2 : b ≤ c)
    (h : a - b + c = d) : x <<< a >>> b <<< c = x <<< d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases hc : i < c <;> by_cases hd : i < d <;> by_cases ha : b + (i - c) < a <;>
    by_cases hw : b + (i - c) < w <;> simp [hc, hd, ha, hi, hw] <;>
    first | omega | (congr 1; omega) | skip
theorem ushr_shl_ushr {w : Nat} (x : BitVec w) (a b c d : Nat) (h1 : b ≤ a) (h2 : b ≤ c)
    (h : a - b + c = d) : x >>> a <<< b >>> c = x >>> d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases hw : c + i < w <;> by_cases hb : c + i < b <;> simp [hw, hb] <;>
    first | omega | (congr 1; omega) |
      exact BitVec.getLsbD_of_ge x _ (by omega)

@[rule_amt] theorem int_emod_eq (a b : Int) : a.emod b = a % b := rfl

attribute [rule_amt] Bool.not_eq_eq_eq_not Bool.not_true decide_eq_false_iff_not decide_eq_true_eq
  Bool.not_false Bool.and_eq_true Bool.or_eq_true

/-! ## Comparisons (`rule_cmp`)

A comparison or equation of `BitVec`s as one of their `toNat`s; a signed value's `toInt` as
its `toNat` minus `2 ^ w` above the sign bit (the `if` is split before `omega`). -/

theorem toInt_omega {w : Nat} (x : BitVec w) :
    x.toInt = if 2 * x.toNat < 2 ^ w then (x.toNat : Int) else (x.toNat : Int) - 2 ^ w :=
  BitVec.toInt_eq_toNat_cond x

/-- What `omega` needs about a right shift (`rule_omega_facts`). -/
theorem ushr_toNat_facts {w : Nat} (x : BitVec w) (n : Nat) :
    (x >>> n).toNat ≤ x.toNat ∧ (0 < n → 2 * (x >>> n).toNat ≤ x.toNat) := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  refine ⟨Nat.div_le_self _ _, fun h => ?_⟩
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) h
  calc 2 * (x.toNat / 2 ^ n) ≤ 2 ^ n * (x.toNat / 2 ^ n) := Nat.mul_le_mul_right _ h2
    _ ≤ x.toNat := Nat.mul_div_le x.toNat (2 ^ n)

attribute [rule_cmp] toInt_omega BitVec.ult_iff_toNat_lt BitVec.ule_iff_toNat_le
  BitVec.slt_iff_toInt_lt BitVec.sle_iff_toInt_le beq_iff_eq bne_iff_ne ne_eq BitVec.toNat_eq
  decide_eq_true_eq Bool.not_eq_true' Bool.true_eq_false Bool.false_eq_true iff_true iff_false
  true_iff false_iff
  Nat.reduceMul Nat.reduceSub Nat.reduceLT ite_true ite_false

@[rule_sem] theorem asNat_retype_of_not_other {t : Ty} {w : Width} (x : BitVec w.bits)
    (h : tyOtherInt t w = false) : ((Val.int w x).retype t).asNat = some x.toNat := by
  cases t with
  | int w' =>
    simp only [tyOtherInt, bne_eq_false_iff_eq] at h
    subst h; simp [Val.retype, Val.asNat, BitVec.setWidth_eq]
  | ptr e =>
    simp only [tyOtherInt, bne_eq_false_iff_eq] at h
    subst h; rfl
  | _ => cases h

@[rule_sem] theorem int64_zero_beq_one : ((0 : Int64) == 1) = false := by decide
@[rule_sem] theorem int64_one_bne_zero : ((1 : Int64) != 0) = true := by decide

/-! ## Conditions -/

@[rule_sem] theorem binE_land_bool (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (b : Bool) (dz : DV) :
    binE vtys .land ty y (.bool b) dz = some (cond b dz (.bool false)) := by
  cases b <;> rfl
@[rule_sem] theorem binE_lor_bool (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (b : Bool) (dz : DV) :
    binE vtys .lor ty y (.bool b) dz = some (cond b (.bool true) dz) := by
  cases b <;> rfl
@[rule_sem] theorem dv_ite_land (b c : Bool) :
    cond b (DV.bool c) (DV.bool false) = DV.bool (b && c) := by cases b <;> rfl
@[rule_sem] theorem dv_ite_lor (b c : Bool) :
    cond b (DV.bool true) (DV.bool c) = DV.bool (b || c) := by cases b <;> rfl
@[rule_sem] theorem dv_land_true (b : Bool) (d : DV) :
    (cond b d (DV.bool false) = DV.bool true) ↔ (b = true ∧ d = DV.bool true) := by
  cases b <;> simp
@[rule_sem] theorem dv_lor_true (b : Bool) (d : DV) :
    (cond b (DV.bool true) d = DV.bool true) ↔ (b = true ∨ d = DV.bool true) := by
  cases b <;> simp
@[rule_sem] theorem binE_eq (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .eq ty y dy dz = binDV .eq (exprTy vtys y) dy dz := rfl
@[rule_sem] theorem binE_ne (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .ne ty y dy dz = binDV .ne (exprTy vtys y) dy dz := rfl
@[rule_sem] theorem binE_lt (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .lt ty y dy dz = binDV .lt (exprTy vtys y) dy dz := rfl
@[rule_sem] theorem binE_le (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .le ty y dy dz = binDV .le (exprTy vtys y) dy dz := rfl
@[rule_sem] theorem binE_gt (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .gt ty y dy dz = binDV .gt (exprTy vtys y) dy dz := rfl
@[rule_sem] theorem binE_ge (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .ge ty y dy dz = binDV .ge (exprTy vtys y) dy dz := rfl
@[rule_sem] theorem binE_add (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .add ty y dy dz = binDV .add ty dy dz := rfl
@[rule_sem] theorem binE_sub (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .sub ty y dy dz = binDV .sub ty dy dz := rfl
@[rule_sem] theorem binE_mul (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .mul ty y dy dz = binDV .mul ty dy dz := rfl
@[rule_sem] theorem binE_quo (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .quo ty y dy dz = binDV .quo ty dy dz := rfl
@[rule_sem] theorem binE_rem (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .rem ty y dy dz = binDV .rem ty dy dz := rfl
@[rule_sem] theorem binE_and (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .and ty y dy dz = binDV .and ty dy dz := rfl
@[rule_sem] theorem binE_or (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .or ty y dy dz = binDV .or ty dy dz := rfl
@[rule_sem] theorem binE_xor (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .xor ty y dy dz = binDV .xor ty dy dz := rfl
@[rule_sem] theorem binE_shl (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .shl ty y dy dz = binDV .shl ty dy dz := rfl
@[rule_sem] theorem binE_shr (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .shr ty y dy dz = binDV .shr ty dy dz := rfl
@[rule_sem] theorem binE_andNot (vtys : List GoTy) (ty : GoTy) (y : GoFV.Rules.Expr) (dy dz : DV) :
    binE vtys .andNot ty y dy dz = binDV .andNot ty dy dz := rfl

/-! ## The op families as `Option.elim` chains

`rule_sem` rewrites the families with these instead of unfolding their `match`es: `simp` then
needs no discharger for the `match` catch-all equations, and a case split on a leaf
(`Val.asInt w (e.leaf p)`) reduces every chain through `Option.elim_none`/`elim_some`. -/

@[rule_sem] theorem int1_eq (w : Width) (f : BitVec w.bits → Val) (a : Val) :
    int1 w f [a] = (a.asInt w).elim .poison f := by
  cases h : a.asInt w <;> simp [int1, h]

@[rule_sem] theorem int2_eq (w : Width) (f : BitVec w.bits → BitVec w.bits → Val) (a b : Val) :
    int2 w f [a, b] = (a.asInt w).elim .poison fun x => (b.asInt w).elim .poison (f x) := by
  cases ha : a.asInt w <;> cases hb : b.asInt w <;> simp [int2, ha, hb]

@[rule_sem] theorem int3_eq (w : Width) (f : BitVec w.bits → BitVec w.bits → BitVec w.bits → Val)
    (a b c : Val) :
    int3 w f [a, b, c] = (a.asInt w).elim .poison fun x => (b.asInt w).elim .poison fun y =>
      (c.asInt w).elim .poison (f x y) := by
  cases ha : a.asInt w <;> cases hb : b.asInt w <;> cases hc : c.asInt w <;> simp [int3, ha, hb, hc]

@[rule_sem] theorem bool1_eq (f : Bool → Bool) (a : Val) :
    bool1 f [a] = a.asBool.elim .poison fun x => .bool (f x) := by
  cases h : a.asBool <;> simp [bool1, h]

@[rule_sem] theorem bool2_eq (f : Bool → Bool → Bool) (a b : Val) :
    bool2 f [a, b] = a.asBool.elim .poison fun x => b.asBool.elim .poison fun y => .bool (f x y) := by
  cases ha : a.asBool <;> cases hb : b.asBool <;> simp [bool2, ha, hb]

@[rule_sem] theorem shift_eq (w a : Width) (bounded : Bool)
    (f : BitVec w.bits → Nat → BitVec w.bits) (x s : Val) :
    Shift.shift w a bounded f [x, s] = (x.asInt w).elim .poison fun x => (s.asInt a).elim .poison
      fun s => if bounded && w.bits ≤ s.toNat then .poison else .int w (f x (min s.toNat w.bits)) := by
  cases hx : x.asInt w <;> cases hs : s.asInt a <;> simp [Shift.shift, hx, hs]

@[rule_sem] theorem rotateLeft_eq (w : Width) (a b : Val) :
    Sem.Int.rotateLeft w [a, b] =
      (a.asInt w).elim .poison fun x => b.asNat.elim .poison fun n => .int w (x.rotateLeft n) := by
  cases ha : a.asInt w <;> cases hb : b.asNat <;> simp [Sem.Int.rotateLeft, ha, hb]

@[rule_sem] theorem condSelect_eq (x y c : Val) :
    Cmp.condSelect [x, y, c] = c.asBool.elim .poison fun b => cond b x y := by
  cases h : c.asBool with
  | none => simp [Cmp.condSelect, h]
  | some b => cases b <;> simp [Cmp.condSelect, h]

@[rule_sem] theorem boolToUint8_eq (b : Val) :
    Conv.boolToUint8 [b] = b.asBool.elim .poison fun b => .i8 (if b then 1 else 0) := by
  cases h : b.asBool <;> simp [Conv.boolToUint8, h]

@[rule_sem] theorem elim_ite_none {α β : Type} (c : Prop) [Decidable c] (x : α) (p : β)
    (f : α → β) : (if c then none else some x).elim p f = if c then p else f x := by
  split <;> rfl

attribute [rule_sem] Option.elim_none Option.elim_some

attribute [rule_sem] Sem.Int.add Sem.Int.sub Sem.Int.mul Sem.Int.and Sem.Int.or Sem.Int.xor
  Sem.Int.neg Sem.Int.com Sem.Int.hmul Sem.Int.mulhilo Sem.Int.mulover Sem.Int.avgu
  Sem.Int.divs Sem.Int.divu Sem.Int.mods Sem.Int.modu Sem.Int.ctz Sem.Int.bitLen
  Sem.Int.popCount Sem.Int.bswap Sem.Int.bitRev Sem.Int.min Sem.Int.max Sem.Int.addcarry
  Sem.Int.subborrow Sem.Int.slicemask Sem.Int.count Sem.Int.div128u Shift.lsh Shift.rsh
  Shift.rshu Cmp.eq Cmp.neq Cmp.less Cmp.lessU Cmp.leq Cmp.leqU Cmp.andB Cmp.orB Cmp.eqB
  Cmp.neqB Cmp.not Cmp.inBounds Cmp.spectreIndex Conv.signExt Conv.zeroExt Conv.trunc
  Conv.constBool Tuple.select Tuple.make Ty.width? Val.asInt_int Width.bits


/-! ## Bitwise identities and constant folds (`rule_close`)

`rule_bits` turns the all-ones constants into `BitVec.allOnes`, after which a bitwise identity
(De Morgan, `~~~x ^^^ x = -1`, …) closes per bit (`ext`, `simp`) for every width. The
`rule_arith` lemmas below push the rules' `c&d`, `c|d`, `c^d` (`GoFV.Rules.bitwise` on 64-bit
patterns) into `BitVec`. -/

@[rule_bits] theorem allOnes8 : (255#8 : BitVec 8) = BitVec.allOnes 8 := by decide
@[rule_bits] theorem allOnes16 : (65535#16 : BitVec 16) = BitVec.allOnes 16 := by decide
@[rule_bits] theorem allOnes32 : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by decide
@[rule_bits] theorem allOnes64 :
    (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 := by decide
attribute [rule_bits] BitVec.neg_one_eq_allOnes

@[rule_arith] theorem ofNat_pat64 {w : Nat} (h : w ≤ 64) (a : Int) :
    BitVec.ofNat w (pat64 a) = BitVec.ofInt w a := by
  rw [(BitVec.ofInt_natCast w (pat64 a)).symm, pat64,
    Int.toNat_of_nonneg (show 0 ≤ a.emod (2 ^ 64) from Int.emod_nonneg _ (by simp))]
  exact ofInt_emod_of_le h a

attribute [rule_arith] GoFV.Rules.bitwise BitVec.ofInt_natCast BitVec.ofNat_and BitVec.ofNat_or
  BitVec.ofNat_xor

/-! ## Extensions, truncations, negated comparisons (#69)

Constant folds of `ZeroExt`/`SignExt`/`Trunc` (`rule_arith`), a retype that keeps an integer of
its own width (`rule_sem`), truncating and re-extending a value whose high bits a shift
cleared or filled with the sign (`rule_ext`), negated comparisons and boolean equations
(`rule_close_s`), low-bit masks as remainders (`rule_amt`). -/

@[rule_sem] theorem retype_int_of_not_other {t : Ty} {w : Width} (x : BitVec w.bits)
    (h : tyOtherInt t w = false) : (Val.int w x).retype t = .int w x := by
  cases t with
  | int w' =>
    simp only [tyOtherInt, bne_eq_false_iff_eq] at h
    subst h; exact retype_int_same w' x
  | ptr e =>
    simp only [tyOtherInt, bne_eq_false_iff_eq] at h
    subst h; rfl
  | _ => simp [tyOtherInt] at h

@[rule_arith] theorem setWidth_ofInt_of_le {w k : Nat} (h : w ≤ k) (c : Int) :
    (BitVec.ofInt w c).setWidth k = BitVec.ofInt k (wrapInt w false c) := by
  apply BitVec.eq_of_toNat_eq
  have hp : 2 ^ w ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) h
  have hw : (0 : Int) < ((2 ^ w : Nat) : Int) := by have := Nat.two_pow_pos w; omega
  have h0 := Int.emod_nonneg c (Int.ne_of_gt hw)
  have h1 := Int.emod_lt_of_pos c hw
  have e : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by simp
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, wrapInt_false, int_emod_eq]
  rw [← e, Int.emod_eq_of_lt h0 (by omega), Nat.mod_eq_of_lt (by omega)]

@[rule_arith] theorem setWidth_ofInt_of_ge {w k : Nat} (h : k ≤ w) (c : Int) :
    (BitVec.ofInt w c).setWidth k = BitVec.ofInt k c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have hd : ((2 ^ k : Nat) : Int) ∣ ((2 ^ w : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h)
  have hw : (0 : Int) < ((2 ^ w : Nat) : Int) := by have := Nat.two_pow_pos w; omega
  have hk : (0 : Int) < ((2 ^ k : Nat) : Int) := by have := Nat.two_pow_pos k; omega
  have h0 := Int.emod_nonneg c (Int.ne_of_gt hw)
  have h0' := Int.emod_nonneg c (Int.ne_of_gt hk)
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.toNat_of_nonneg h0, Int.toNat_of_nonneg h0']
  exact Int.emod_emod_of_dvd c hd

@[rule_arith] theorem signExtend_ofInt {w k : Nat} (h : w ≤ k) (c : Int) :
    (BitVec.ofInt w c).signExtend k = BitVec.ofInt k (wrapInt w true c) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le h, wrapInt_true, BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  have hp : 2 ^ w ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) h
  have l := Int.le_bmod (x := c) (Nat.two_pow_pos w)
  have u := Int.bmod_lt (x := c) (Nat.two_pow_pos w)
  rw [Int.bmod_eq_of_le (n := c.bmod (2 ^ w)) (m := 2 ^ k)] <;> omega

theorem ushr_setWidth_setWidth {w k n : Nat} (x : BitVec w) (hk : k ≤ w) (hn : w - k ≤ n) :
    ((x >>> n).setWidth k).setWidth w = x >>> n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases hik : i < k
  · simp [hik, hi]
  · simp only [hik, decide_false, Bool.false_and]
    rw [BitVec.getLsbD_of_ge x _ (by omega)]; simp

theorem sshr_setWidth_signExtend {w k n : Nat} (x : BitVec w) (hk0 : 0 < k) (hk : k ≤ w)
    (hn : w - k ≤ n) : ((x.sshiftRight n).setWidth k).signExtend w = x.sshiftRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_signExtend, BitVec.msb_setWidth]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight, hi, decide_true,
    Bool.true_and, hk0]
  by_cases hik : i < k
  · simp [hik, show ¬ w ≤ i by omega]
  · simp only [hik, ite_false, Bool.true_and, show ¬ w ≤ k - 1 by omega,
      show ¬ w ≤ i by omega, decide_false, Bool.not_false, show ¬ n + i < w by omega]
    by_cases h2 : n + (k - 1) < w
    · simp only [h2, ite_true]
      have : n + (k - 1) = w - 1 := by omega
      rw [this, BitVec.msb_eq_getLsbD_last]
    · simp [h2]

theorem not_slt_eq {w : Nat} (x y : BitVec w) : (!x.slt y) = y.sle x := by
  simp only [BitVec.sle, BitVec.slt]; cases h : decide (y.toInt ≤ x.toInt) <;> simp_all <;> omega
theorem not_sle_eq {w : Nat} (x y : BitVec w) : (!x.sle y) = y.slt x := by
  simp only [BitVec.sle, BitVec.slt]; cases h : decide (y.toInt < x.toInt) <;> simp_all <;> omega
theorem not_ult_eq {w : Nat} (x y : BitVec w) : (!x.ult y) = y.ule x := by
  simp only [BitVec.ule, BitVec.ult]; cases h : decide (y.toNat ≤ x.toNat) <;> simp_all <;> omega
theorem not_ule_eq {w : Nat} (x y : BitVec w) : (!x.ule y) = y.ult x := by
  simp only [BitVec.ule, BitVec.ult]; cases h : decide (y.toNat < x.toNat) <;> simp_all <;> omega
theorem not_beq_eq (a b : Bool) : ((!a) == b) = (a != b) := by cases a <;> cases b <;> rfl
theorem not_bne_eq (a b : Bool) : ((!a) != b) = (a == b) := by cases a <;> cases b <;> rfl

attribute [rule_close_s] not_slt_eq not_sle_eq not_ult_eq not_ule_eq not_beq_eq not_bne_eq

@[rule_amt] theorem nat_and_255 (a : Nat) : a &&& 255 = a % 256 :=
  Nat.and_two_pow_sub_one_eq_mod a 8
@[rule_amt] theorem nat_and_65535 (a : Nat) : a &&& 65535 = a % 65536 :=
  Nat.and_two_pow_sub_one_eq_mod a 16
@[rule_amt] theorem nat_and_4294967295 (a : Nat) : a &&& 4294967295 = a % 4294967296 :=
  Nat.and_two_pow_sub_one_eq_mod a 32


/-! ## Division and remainder (#69)

Constant folds of `Div`/`Mod` (`sdiv_ofInt`, `srem_ofInt`: Go's truncated `/`, `%` on auxints in
range; `udiv_ofInt`, `umod_ofInt` on the low bits), `x % y = x - (x / y) * y`
(`sub_udiv_mul`, `sub_sdiv_mul`), division by a negated or minimal constant (`rule_div`). -/

theorem toInt_ofInt_of_range {w : Nat} {c : Int} (h1 : -(((2 ^ w : Nat) : Int) / 2) ≤ c)
    (h2 : c < (((2 ^ w : Nat) : Int) + 1) / 2) : (BitVec.ofInt w c).toInt = c := by
  rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le h1 h2

theorem sdiv_ofInt {w : Nat} {c d : Int} (h1 : -(((2 ^ w : Nat) : Int) / 2) ≤ c)
    (h2 : c < (((2 ^ w : Nat) : Int) + 1) / 2) (h3 : -(((2 ^ w : Nat) : Int) / 2) ≤ d)
    (h4 : d < (((2 ^ w : Nat) : Int) + 1) / 2) :
    (BitVec.ofInt w c).sdiv (BitVec.ofInt w d) = BitVec.ofInt w (goQuo c d) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv, toInt_ofInt_of_range h1 h2, toInt_ofInt_of_range h3 h4,
    BitVec.toInt_ofInt]
  rfl

theorem tmod_range (c d : Int) : (0 ≤ c → 0 ≤ c.tmod d ∧ c.tmod d ≤ c) ∧
    (c < 0 → c ≤ c.tmod d ∧ c.tmod d ≤ 0) := by
  have key : ∀ a : Int, 0 ≤ a → 0 ≤ a % d ∧ a % d ≤ a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg d
    · rw [← Int.natCast_emod]; exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (Nat.mod_le n k)⟩
    · rw [Int.emod_neg, ← Int.natCast_emod]
      exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (Nat.mod_le n k)⟩
  obtain ⟨f1, f2⟩ := tmod_facts c d
  constructor
  · intro hc; rw [f1 hc]; exact key c hc
  · intro hc; rw [f2 hc]; have := key (-c) (by omega); omega

theorem srem_ofInt {w : Nat} {c d : Int} (h1 : -(((2 ^ w : Nat) : Int) / 2) ≤ c)
    (h2 : c < (((2 ^ w : Nat) : Int) + 1) / 2) (h3 : -(((2 ^ w : Nat) : Int) / 2) ≤ d)
    (h4 : d < (((2 ^ w : Nat) : Int) + 1) / 2) :
    (BitVec.ofInt w c).srem (BitVec.ofInt w d) = BitVec.ofInt w (goRem c d) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_srem, toInt_ofInt_of_range h1 h2, toInt_ofInt_of_range h3 h4,
    BitVec.toInt_ofInt]
  have := tmod_range c d
  unfold goRem
  rw [Int.bmod_eq_of_le] <;> omega

/-- The low `w` bits of `c` as a natural number below `2 ^ w`. -/
theorem emod_pow_nat (w : Nat) (c : Int) :
    ∃ n : Nat, c % 2 ^ w = n ∧ n < 2 ^ w ∧ (BitVec.ofInt w c).toNat = n := by
  have hp : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)
  have h0 := Int.emod_nonneg c (Int.ne_of_gt hp)
  have h1 := Int.emod_lt_of_pos c hp
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h0
  refine ⟨n, hn, ?_, ?_⟩
  · have : (n : Int) < ((2 ^ w : Nat) : Int) := by rw [← hn]; simpa using h1
    exact_mod_cast this
  · rw [BitVec.toNat_ofInt]
    have : ((2 ^ w : Nat) : Int) = 2 ^ w := by simp
    rw [this, hn]; rfl

theorem udiv_ofInt (w : Nat) (c d : Int) :
    BitVec.ofInt w c / BitVec.ofInt w d =
      BitVec.ofInt w (goQuo (wrapInt w false c) (wrapInt w false d)) := by
  apply BitVec.eq_of_toNat_eq
  obtain ⟨n, hn, hnl, hnt⟩ := emod_pow_nat w c
  obtain ⟨k, hk, hkl, hkt⟩ := emod_pow_nat w d
  rw [BitVec.toNat_udiv, hnt, hkt, wrapInt_false, wrapInt_false, int_emod_eq, int_emod_eq, hn, hk,
    goQuo, Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg _), ← Int.natCast_ediv]
  obtain ⟨m, hm, hml, hmt⟩ := emod_pow_nat w ((n / k : Nat) : Int)
  rw [hmt]
  have : ((n / k : Nat) : Int) % 2 ^ w = ((n / k : Nat) : Int) := by
    apply Int.emod_eq_of_lt (Int.natCast_nonneg _)
    have : n / k < 2 ^ w := Nat.lt_of_le_of_lt (Nat.div_le_self n k) hnl
    have : ((n / k : Nat) : Int) < ((2 ^ w : Nat) : Int) := by exact_mod_cast this
    simpa using this
  rw [this] at hm
  exact_mod_cast hm

theorem umod_ofInt (w : Nat) (c d : Int) :
    BitVec.ofInt w c % BitVec.ofInt w d =
      BitVec.ofInt w (goRem (wrapInt w false c) (wrapInt w false d)) := by
  apply BitVec.eq_of_toNat_eq
  obtain ⟨n, hn, hnl, hnt⟩ := emod_pow_nat w c
  obtain ⟨k, hk, hkl, hkt⟩ := emod_pow_nat w d
  rw [BitVec.toNat_umod, hnt, hkt, wrapInt_false, wrapInt_false, int_emod_eq, int_emod_eq, hn, hk,
    goRem, Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg _), ← Int.natCast_emod]
  obtain ⟨m, hm, hml, hmt⟩ := emod_pow_nat w ((n % k : Nat) : Int)
  rw [hmt]
  have : ((n % k : Nat) : Int) % 2 ^ w = ((n % k : Nat) : Int) := by
    apply Int.emod_eq_of_lt (Int.natCast_nonneg _)
    have : n % k < 2 ^ w := Nat.lt_of_le_of_lt (Nat.mod_le n k) hnl
    have : ((n % k : Nat) : Int) < ((2 ^ w : Nat) : Int) := by exact_mod_cast this
    simpa using this
  rw [this] at hm
  exact_mod_cast hm

theorem sub_udiv_mul {w : Nat} (x y : BitVec w) : x - x / y * y = x % y := by
  rw [BitVec.sub_eq_iff_eq_add]
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have h1 : x.toNat / y.toNat * y.toNat ≤ x.toNat := Nat.div_mul_le_self _ _
  have h2 := Nat.mod_add_div x.toNat y.toNat
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_umod]
  rw [Nat.mod_eq_of_lt (a := x.toNat / y.toNat * y.toNat) (by omega)]
  rw [Nat.mod_eq_of_lt (by rw [Nat.mul_comm] at h2; omega)]
  rw [Nat.mul_comm] at h2; omega

theorem sub_sdiv_mul {w : Nat} (x y : BitVec w) : x - x.sdiv y * y = x.srem y := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sub, BitVec.toInt_mul, BitVec.toInt_sdiv, BitVec.toInt_srem, Int.sub_bmod_bmod,
    Int.sub_bmod, Int.bmod_mul_bmod, ← Int.sub_bmod, Int.mul_comm, ← Int.tmod_def,
    ← BitVec.toInt_srem, BitVec.toInt_bmod_cancel]

theorem srem_neg_right {w : Nat} (x y : BitVec w) : x.srem (-y) = x.srem y := by
  by_cases h : y = BitVec.intMin w
  · subst h; rw [BitVec.neg_intMin]
  · apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_srem, BitVec.toInt_srem, BitVec.toInt_neg_of_ne_intMin h, Int.tmod_neg]

theorem ofInt_ne_intMin {w : Nat} {c : Int} (h1 : -(((2 ^ w : Nat) : Int) / 2) ≤ c)
    (h2 : c < (((2 ^ w : Nat) : Int) + 1) / 2) (h3 : c ≠ -(((2 ^ w : Nat) : Int) / 2)) :
    BitVec.ofInt w c ≠ BitVec.intMin w := by
  intro h
  have := congrArg BitVec.toInt h
  rw [toInt_ofInt_of_range h1 h2] at this
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw; simp at h1 h2; omega
  · rw [BitVec.toInt_intMin_of_pos hw] at this
    have e : ((2 ^ w : Nat) : Int) / 2 = ((2 ^ (w - 1) : Nat) : Int) := by
      rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]; simp
    rw [e] at h3
    exact h3 (by rw [this]; simp)

theorem sdiv_neg_ofInt {w : Nat} {c : Int} (x : BitVec w)
    (h1 : -(((2 ^ w : Nat) : Int) / 2) ≤ c) (h2 : c < (((2 ^ w : Nat) : Int) + 1) / 2)
    (h3 : c ≠ -(((2 ^ w : Nat) : Int) / 2)) :
    x.sdiv (-BitVec.ofInt w c) = -(x.sdiv (BitVec.ofInt w c)) :=
  BitVec.sdiv_neg (ofInt_ne_intMin h1 h2 h3)

theorem ushr_pred_eq_msb {w : Nat} (hw : 0 < w) (y : BitVec w) :
    y >>> (w - 1) = if y.msb then 1#w else 0#w := by
  apply BitVec.eq_of_toNat_eq
  have hy := y.isLt
  have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have h1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_toNat]
  by_cases h : y.toNat ≥ 2 ^ (w - 1)
  · simp only [h, decide_true, ite_true, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
    apply Nat.div_eq_of_lt_le <;> omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, BitVec.toNat_ofNat, Nat.zero_mod]
    exact Nat.div_eq_of_lt (by omega)

theorem sdiv_intMin_and_neg {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x.sdiv (BitVec.intMin w) = (x &&& -x) >>> (w - 1) := by
  rw [BitVec.sdiv_intMin, ushr_pred_eq_msb hw]
  by_cases h : x = BitVec.intMin w
  · subst h; simp [BitVec.neg_intMin, BitVec.msb_intMin, hw]
  · simp only [h, ite_false, BitVec.msb_and, BitVec.msb_neg]
    by_cases h0 : x = 0#w
    · subst h0; simp
    · cases hm : x.msb <;> simp [h, h0]

@[rule_bits] theorem intMin8 : (-128#8 : BitVec 8) = BitVec.intMin 8 := by decide
@[rule_bits] theorem intMin16 : (-32768#16 : BitVec 16) = BitVec.intMin 16 := by decide
@[rule_bits] theorem intMin32 : (-2147483648#32 : BitVec 32) = BitVec.intMin 32 := by decide
@[rule_bits] theorem intMin64 :
    (-9223372036854775808#64 : BitVec 64) = BitVec.intMin 64 := by decide


/-! ## Division by powers of two (`rule_pow2`)

`isPowerOfTwo(uintN(c))` makes the divisor `2 ^ (bitsLen c - 1)` (`isPow2_toNat`); an unsigned
division is then a shift (`udiv_pow2`), a remainder a mask (`umod_pow2_and`). -/
theorem testBit_of_range {x k : Nat} (h1 : 2 ^ k ≤ x) (h2 : x < 2 ^ (k + 1)) :
    x.testBit k = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  have hp := Nat.two_pow_pos k
  have : x / 2 ^ k = 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.pow_succ] at h2; omega
  rw [this]

theorem pow2_of_and_pred {d : Nat} (h0 : 0 < d) (h : d &&& (d - 1) = 0) :
    d = 2 ^ (bitsLen d - 1) := by
  have hb : bitsLen d - 1 = d.log2 := by unfold bitsLen; simp [Nat.ne_of_gt h0]
  rw [hb]
  have hl := Nat.log2_self_le (Nat.ne_of_gt h0)
  have hu : d < 2 ^ (d.log2 + 1) := Nat.lt_log2_self
  false_or_by_contra
  rename_i hne
  have h1 : d.testBit d.log2 = true := testBit_of_range hl hu
  have h2 : (d - 1).testBit d.log2 = true := testBit_of_range (by omega) (by omega)
  have : (d &&& (d - 1)).testBit d.log2 = true := by rw [Nat.testBit_and, h1, h2]; rfl
  rw [h] at this
  simp at this

theorem udiv_pow2 {w : Nat} (x y : BitVec w) (k : Nat) (h : y.toNat = 2 ^ k) :
    x / y = x >>> k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h]

theorem umod_pow2_and {w : Nat} (x y : BitVec w) (k : Nat) (h : y.toNat = 2 ^ k) :
    x % y = x &&& (y - 1#w) := by
  apply BitVec.eq_of_toNat_eq
  have hy := y.isLt
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0; simp at hy; omega
    · exact h0
  have h1 : (1#w).toNat = 1 := by simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt hw))]
  rw [BitVec.toNat_umod, BitVec.toNat_and, BitVec.toNat_sub, h, h1]
  rw [show 2 ^ w - 1 + 2 ^ k = (2 ^ k - 1) + 2 ^ w by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (a := 2 ^ k - 1) (by omega), Nat.and_two_pow_sub_one_eq_mod]

/-- A product with a power of two is a left shift (`generic.rules:1106–1112`). -/
theorem mul_pow2 {w : Nat} (x y : BitVec w) (k : Nat) (h : y.toNat = 2 ^ k) :
    x * y = x <<< k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_shiftLeft, h, Nat.shiftLeft_eq]

/-- A product with a negated power of two is a negated left shift (`generic.rules:1114–1120`). -/
theorem mul_negpow2 {w : Nat} (x y : BitVec w) (k : Nat) (h : (-y).toNat = 2 ^ k) :
    x * y = -(x <<< k) := by
  rw [← mul_pow2 x (-y) k h, BitVec.mul_neg, BitVec.neg_neg]

/-- `uintN(-c)` as a `BitVec`: the negation of `c`'s. -/
theorem ofInt_wrap_neg {w : Nat} (c : Int) :
    BitVec.ofInt w (wrapInt w true (-c)) = -BitVec.ofInt w c := by
  rw [ofInt_wrapInt_true (Nat.le_refl w), BitVec.ofInt_neg]


theorem isPow2_toNat {T : GoTy} {w : Nat} {c : Int} (hT : T.intInfo? = some (w, false))
    (hw : w ≤ 64) (h0 : 0 < wrapInt w false c)
    (h : wrapInt w false (andPred T (wrapInt w false c)) = 0) :
    (BitVec.ofInt w c).toNat = 2 ^ (bitsLen (wrapInt w false c).toNat - 1) ∧
      1 ≤ bitsLen (wrapInt w false c).toNat ∧ bitsLen (wrapInt w false c).toNat ≤ w := by
  obtain ⟨n, hn, hnl, hnt⟩ := emod_pow_nat w c
  have hd : wrapInt w false c = n := by rw [wrapInt_false]; exact hn
  rw [hd] at h0 h ⊢
  rw [hnt, Int.toNat_natCast]
  have hn0 : 0 < n := by omega
  have h64 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  have hp1 : pat64 (n : Int) = n := by
    unfold pat64
    rw [show (n : Int).emod (2 ^ 64) = (n : Int) % ((2 ^ 64 : Nat) : Int) by simp; rfl,
      ← Int.natCast_emod, Int.toNat_natCast, Nat.mod_eq_of_lt (by omega)]
  have hp2 : pat64 ((n : Int) - 1) = n - 1 := by
    rw [show (n : Int) - 1 = ((n - 1 : Nat) : Int) by omega]
    unfold pat64
    rw [show ((n - 1 : Nat) : Int).emod (2 ^ 64) = ((n - 1 : Nat) : Int) % ((2 ^ 64 : Nat) : Int)
      by simp; rfl, ← Int.natCast_emod, Int.toNat_natCast, Nat.mod_eq_of_lt (by omega)]
  unfold andPred bitwise at h
  rw [hT] at h
  simp only [Option.getD_some, hp1, hp2] at h
  have hand : n &&& (n - 1) < 2 ^ w := Nat.lt_of_le_of_lt Nat.and_le_left hnl
  have hk : ((n &&& (n - 1) : Nat) : Int) % 2 ^ w = ((n &&& (n - 1) : Nat) : Int) := by
    apply Int.emod_eq_of_lt (Int.natCast_nonneg _)
    have : ((n &&& (n - 1) : Nat) : Int) < ((2 ^ w : Nat) : Int) := by exact_mod_cast hand
    simpa using this
  have hz : n &&& (n - 1) = 0 := by
    simp only [wrapInt_false, int_emod_eq, hk] at h
    omega
  refine ⟨pow2_of_and_pred hn0 hz, ?_, ?_⟩
  · unfold bitsLen; simp [Nat.ne_of_gt hn0]
  · unfold bitsLen
    simp only [Nat.ne_of_gt hn0, ite_false]
    have := (Nat.log2_lt (Nat.ne_of_gt hn0)).mpr hnl
    omega

/-- `isPowerOfTwo(c)` of a signed `c` (`T` a signed type): `c` is `2 ^ k` with `k + 1 < w`. -/
theorem isPow2_signed {T : GoTy} {w : Nat} {c : Int} (hT : T.intInfo? = some (w, true))
    (hw : w ≤ 64) (h0 : 0 < c) (hhi : c < (((2 ^ w : Nat) : Int) + 1) / 2)
    (h : wrapInt w true (andPred T c) = 0) :
    ∃ k, (BitVec.ofInt w c).toNat = 2 ^ k ∧ k + 1 < w := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, c = n := ⟨c.toNat, by omega⟩
  have hn0 : 0 < n := by omega
  have hp := Nat.two_pow_pos w
  have h64 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  have hn2 : 2 * n < 2 ^ w := by omega
  have hp1 : pat64 (n : Int) = n := by
    unfold pat64
    rw [show (n : Int).emod (2 ^ 64) = (n : Int) % ((2 ^ 64 : Nat) : Int) by simp; rfl,
      ← Int.natCast_emod, Int.toNat_natCast, Nat.mod_eq_of_lt (by omega)]
  have hp2 : pat64 ((n : Int) - 1) = n - 1 := by
    rw [show (n : Int) - 1 = ((n - 1 : Nat) : Int) by omega]
    unfold pat64
    rw [show ((n - 1 : Nat) : Int).emod (2 ^ 64) = ((n - 1 : Nat) : Int) % ((2 ^ 64 : Nat) : Int)
      by simp; rfl, ← Int.natCast_emod, Int.toNat_natCast, Nat.mod_eq_of_lt (by omega)]
  unfold andPred bitwise at h
  rw [hT] at h
  simp only [Option.getD_some, hp1, hp2] at h
  have hand : n &&& (n - 1) ≤ n - 1 := Nat.and_le_right
  have hz : n &&& (n - 1) = 0 := by
    have hb : ∀ x : Nat, 2 * x < 2 ^ w → wrapInt w true (x : Int) = x := by
      intro x hx
      rw [wrapInt_true]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    rw [hb _ (by omega), hb _ (by omega)] at h
    omega
  have hn := pow2_of_and_pred hn0 hz
  refine ⟨bitsLen n - 1, ?_, ?_⟩
  · rw [BitVec.toNat_ofInt]
    rw [show ((n : Int) % ((2 ^ w : Nat) : Int)) = ((n % 2 ^ w : Nat) : Int) by push_cast; rfl]
    rw [Int.toNat_natCast, Nat.mod_eq_of_lt (by omega)]
    exact hn
  · rw [hn] at hn2
    have : 2 ^ (bitsLen n - 1 + 1) < 2 ^ w := by rw [Nat.pow_succ]; omega
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this

theorem beq_eq_sub_beq {w : Nat} (x z : BitVec w) : (x == z) = (x - z == 0#w) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]

theorem and_pred_pow2 {w : Nat} (x y : BitVec w) (k : Nat) (h : y.toNat = 2 ^ k) :
    (x &&& y - 1#w).toNat = x.toNat % 2 ^ k := by
  rw [← umod_pow2_and x y k h, BitVec.toNat_umod, h]

/-- `x == x / y * y` for `y = 2 ^ k`: the low `k` bits of `x` are zero (`divisible.rules:17`). -/
theorem divisible_pow2_u {w : Nat} (x y : BitVec w) (k : Nat) (h : y.toNat = 2 ^ k) :
    (x == x / y * y) = (x &&& y - 1#w == 0#w) := by
  rw [beq_eq_sub_beq, sub_udiv_mul, umod_pow2_and x y k h]

/-- The signed form (`divisible.rules:20`): `y = 2 ^ k` is positive, `x.srem y = 0` iff
`2 ^ k` divides `x.toInt` iff it divides `x.toNat`. -/
theorem divisible_pow2_s {w : Nat} (x y : BitVec w) (k : Nat) (h : y.toNat = 2 ^ k)
    (hk : k + 1 < w) : (x == x.sdiv y * y) = (x &&& y - 1#w == 0#w) := by
  rw [beq_eq_sub_beq, sub_sdiv_mul, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq,
    ← BitVec.toInt_inj, BitVec.toInt_srem, ← BitVec.toNat_inj, and_pred_pow2 x y k h]
  have hyi : y.toInt = ((2 ^ k : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_of_msb, h]
    rw [BitVec.msb_eq_decide, h]
    have : 2 ^ k < 2 ^ (w - 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    simp only [decide_eq_false_iff_not, Nat.not_le]
    exact Nat.lt_of_lt_of_le this (Nat.le_refl _)
  have hkw : ((2 ^ k : Nat) : Int) ∣ ((2 ^ w : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 (by omega))
  have hx := x.isLt
  rw [hyi, BitVec.toInt_zero, BitVec.toNat_zero, ← Int.dvd_iff_tmod_eq_zero,
    Int.dvd_iff_emod_eq_zero, ← Int.emod_emod_of_dvd x.toInt hkw, BitVec.toInt_eq_toNat_bmod,
    Int.bmod_emod, ← Int.natCast_emod, ← Int.natCast_emod, Nat.mod_eq_of_lt hx]
  omega

theorem divisible_pow2_u_ne {w : Nat} (x y : BitVec w) (k : Nat) (h : y.toNat = 2 ^ k) :
    (x != x / y * y) = (x &&& y - 1#w != 0#w) := by
  rw [bne, bne, divisible_pow2_u x y k h]

theorem divisible_pow2_s_ne {w : Nat} (x y : BitVec w) (k : Nat) (h : y.toNat = 2 ^ k)
    (hk : k + 1 < w) : (x != x.sdiv y * y) = (x &&& y - 1#w != 0#w) := by
  rw [bne, bne, divisible_pow2_s x y k h hk]

/-- A comparison's evaluation with the `bool` oracle as fallback is a boolean, whatever its
operands (`rule_cond_bool`: `x.Op != OpConst64` on an oracle answer). -/
theorem binDV_cmp_bool {o : BinOp}
    (ho : o = .eq ∨ o = .ne ∨ o = .lt ∨ o = .le ∨ o = .gt ∨ o = .ge) (ty : GoTy) (X Y : DV)
    (w : Bool) : ∃ b, (binDV o ty X Y).getD (.bool w) = .bool b := by
  have hi : ∀ a b, ∃ c, (intBin o ty a b).getD (.bool w) = .bool c := by
    intro a b
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  cases X <;> cases Y <;> first
    | exact hi _ _
    | exact ⟨_, rfl⟩
    | (cases o <;> exact ⟨_, rfl⟩)
    | (rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)

/-! ## Pointers (`Pat.argsOK`; `generic.rules:964`, `:965`, `:970`) -/

theorem isPtrTy_iff {t : Ty} : isPtrTy t = true ↔ ∃ el, t = .ptr el := by
  unfold isPtrTy; split <;> simp_all

theorem isInt64Ty_iff {t : Ty} : isInt64Ty t = true ↔ t = .int .w64 := by
  unfold isInt64Ty; split <;> simp_all

theorem isIntWTy_iff {w : Width} {t : Ty} : isIntWTy w t = true ↔ t = .int w := by
  cases w <;> cases t <;> simp [isIntWTy] <;> rename_i w' <;> cases w' <;> simp

theorem isSliceTy_iff {t : Ty} : isSliceTy t = true ↔ ∃ el, t = .slice el := by
  unfold isSliceTy; split <;> simp_all

/-! ## `isNonNegative` leaves (`Pat.nonNegOK`) -/

@[rule_sem] theorem nonNeg_int (w : Width) (x : BitVec w.bits) : (Val.int w x).nonNeg = !x.msb :=
  rfl

@[rule_sem] theorem nonNeg_poison : Val.poison.nonNeg = true := rfl

/-- A word shape (a pointer shape or the 64-bit integer shape, `argShapeOk` of `OffPtr` and
`IsNonNil`) has the values and the retyping of `.ptr none`. -/
theorem wordShape_ptr {t : Ty} (h : (∃ el, t = .ptr el) ∨ t = .int .w64) :
    (∀ v : Val, v.retype t = v.retype (.ptr none)) ∧ (∀ v : Val, v.hasTy t = v.hasTy (.ptr none)) := by
  rcases h with ⟨el, rfl⟩ | rfl
  · exact ⟨fun v => by rw [Val.retype_ptr_eq_i64 v el, Val.retype_ptr_eq_i64 v none],
      fun v => by rw [Val.hasTy_ptr_eq_i64 v el, Val.hasTy_ptr_eq_i64 v none]⟩
  · exact ⟨fun v => (Val.retype_ptr_eq_i64 v none).symm, fun v => (Val.hasTy_ptr_eq_i64 v none).symm⟩

/-- A value of a pointer shape is `poison`, a 64-bit integer (the pointer at that address) or a
pointer. -/
theorem val_of_hasTy_ptr {a : Val} {el : Option Nat} (h : a.hasTy (.ptr el) = true) :
    a = .poison ∨ (∃ x, a = .int .w64 x) ∨ ∃ p, a = .ptr p := by
  cases a with
  | int w x => cases w <;> first | exact .inr (.inl ⟨x, rfl⟩) | simp [Val.hasTy] at h
  | ptr p => exact .inr (.inr ⟨p, rfl⟩)
  | poison => exact .inl rfl
  | _ => simp [Val.hasTy] at h

/-- A value of the 64-bit integer shape is `poison`, an integer, or a pointer that does not
convert to an integer. -/
theorem val_of_hasTy_int64 {a : Val} (h : a.hasTy (.int .w64) = true) :
    a = .poison ∨ (∃ x, a = .int .w64 x) ∨ ∃ p, a = .ptr p ∧ p.convertible = false := by
  cases a with
  | poison => exact .inl rfl
  | int w x => cases w <;> first | exact .inr (.inl ⟨x, rfl⟩) | simp [Val.hasTy] at h
  | ptr p => exact .inr (.inr ⟨p, rfl, Ptr.not_convertible_of_held (by simpa [Val.hasTy] using h)⟩)
  | _ => simp [Val.hasTy] at h

theorem ptr_add_add (p : Ptr) (a b : BitVec 64) : (p.add a).add b = p.add (a + b) := by
  simp [Ptr.add, BitVec.add_assoc]

/-- A value refines its retyping at a shape it has. -/
theorem refines_retype_of_hasTy {v : Val} {t : Ty} (h : v.hasTy t = true) :
    Refines v (v.retype t) := by
  rw [Val.retype_of_hasTy h]; exact Refines.refl _

/-- A pointer-arithmetic result refines the pointer's word (it is the word or `poison`, #156). -/
theorem ptrRes_refines (p : Ptr) : Refines (PtrOps.ptrRes p) p.word := by
  unfold PtrOps.ptrRes; split
  · exact Refines.refl _
  · exact Refines.poison _

theorem retype_ptrRes_ptr (e : Option Nat) (p : Ptr) :
    (PtrOps.ptrRes p).retype (.ptr e) = PtrOps.ptrRes p := by
  unfold PtrOps.ptrRes; split
  · exact Ptr.word_retype_ptr _ e
  · rfl

/-- `OffPtr` of a pointer-arithmetic result: `poison` if the first step left the window. -/
theorem offPtr_ptrRes (k : Int64) (q : Ptr) :
    PtrOps.offPtr k [PtrOps.ptrRes q] =
      if q.inWindow then PtrOps.ptrRes (q.add (BitVec.ofInt 64 k.toInt)) else .poison := by
  by_cases h : q.inWindow = true
  · rw [if_pos h, show PtrOps.ptrRes q = q.word from if_pos h, PtrOps.offPtr_word _ h]; rfl
  · rw [if_neg h, show PtrOps.ptrRes q = .poison from if_neg h]; rfl

/-- Two steps of pointer arithmetic refine one step by the sum (the intermediate pointer may
leave the window where the sum does not). -/
theorem ptrRes_two_steps (p : Ptr) (a b : BitVec 64) (t : Ty) :
    Refines ((if (p.add a).inWindow then PtrOps.ptrRes ((p.add a).add b) else .poison).retype t)
      ((PtrOps.ptrRes (p.add (a + b))).retype t) := by
  split
  · rw [ptr_add_add]; exact Refines.refl _
  · rw [Val.retype]; exact Refines.poison _

/-! ## Constant composites (`generic.rules:1044`, `:1057`) -/

theorem ty_of_hasTy_int64 {t : Ty} {x : BitVec 64} (h : (Val.int .w64 x).hasTy t = true) :
    t = .int .w64 ∨ ∃ el, t = .ptr el := by
  cases t with
  | int w => cases w <;> first | exact .inl rfl | simp [Val.hasTy] at h
  | ptr el => exact .inr ⟨el, rfl⟩
  | _ => simp [Val.hasTy] at h

theorem ty_of_hasTy_agg {vs : List Val} {t : Ty} (h : (Val.agg vs).hasTy t = true) :
    (∃ fs n, t = .agg fs n ∧ Val.hasTyList vs (fs.map (·.2)) = true) ∨ t = .str ∨
      ∃ e, t = .slice e := by
  cases t with
  | agg fs n => exact .inl ⟨fs, n, rfl, h⟩
  | str => exact .inr (.inl rfl)
  | slice e => exact .inr (.inr ⟨e, rfl⟩)
  | _ => simp [Val.hasTy] at h

/-! ## Nil comparisons (`generic.rules:1683`, `:1684`) -/

/-- A pointer equals the nil pointer iff it is nil (`Ptr.eq` compares block and offset). -/
theorem null_eq (p : Ptr) : Ptr.null.eq p = p.isNil := by
  simp only [Ptr.eq, Ptr.null, Ptr.isNil]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩

/-- `Ptr.ofAddr` gives the nil pointer exactly at address 0. -/
theorem ofAddr_isNil (x : BitVec 64) : (Ptr.ofAddr x).isNil = (x == 0) := by
  have hx := x.isLt
  by_cases h1 : x.toNat < 2 ^ 40
  · simp [Ptr.ofAddr, h1, Ptr.isNil]
  have hne : (x == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; subst h; simp at h1
  rw [hne]
  by_cases h2 : x.toNat < 2 ^ 62
  · simp [Ptr.ofAddr, h1, h2, Ptr.isNil]
  · unfold Ptr.ofAddr
    simp only [h1, h2, ↓reduceIte]
    split <;> simp [Ptr.isNil]

/-- A value of a pointer-word shape (a pointer or a 64-bit integer) is `poison`, a 64-bit
integer or a pointer. -/
theorem val_of_hasTy_word {a : Val} {t : Ty} (ht : (∃ el, t = .ptr el) ∨ t = .int .w64)
    (h : a.hasTy t = true) : a = .poison ∨ (∃ x, a = .int .w64 x) ∨ ∃ p, a = .ptr p := by
  rcases ht with ⟨el, rfl⟩ | rfl
  · exact val_of_hasTy_ptr h
  · rcases val_of_hasTy_int64 h with h | h | ⟨p, h, -⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨p, h⟩)

/-- The nil constant (the word 0, `Ptr.null_word`) at a pointer-word shape reads as the nil
pointer. -/
theorem null_word {t : Ty} (ht : (∃ el, t = .ptr el) ∨ t = .int .w64) :
    ((Val.i64 0).retype t).asPtrWord = some Ptr.null := by
  rw [show Val.i64 0 = Ptr.null.word from Ptr.null_word.symm]
  rcases ht with ⟨el, rfl⟩ | rfl
  · rw [Ptr.word_retype_ptr, Ptr.word_asPtrWord rfl]
  · rw [Ptr.word_retype_i64, Ptr.word_asPtrWord rfl]

theorem not_beq_bne {α : Type} [BEq α] (a b : α) : (!(a == b)) = (a != b) := rfl

end GoFV.Proof.Rules
