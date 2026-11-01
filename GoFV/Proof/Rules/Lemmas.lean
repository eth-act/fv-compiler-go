import GoFV.Proof.Rules.Attr
import GoFV.Proof.Rules.Den

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

/-- A value of shape `Ty.int w` that is not a `w`-bit integer is `poison`. -/
theorem val_poison_of_asInt_none {v : Val} {w : Width} (h : v.asInt w = none)
    (ht : v.hasTy (.int w) = true) : v = .poison := by
  cases v with
  | poison => rfl
  | int w' x =>
    simp only [Val.hasTy, beq_iff_eq] at ht
    subst ht; simp at h
  | _ => simp [Val.hasTy] at ht

/-- An integer of width `w` read back at `w` through a retype to `t` fails: `t` is an integer
shape of another width (narrower: the low bits; wider: `poison`), `bool` (`poison`) or, for
`w = 64`, a pointer shape (`Val.retype`). -/
def tyOtherInt (t : Ty) (w : Width) : Bool :=
  match t with
  | .int w' => w' != w
  | .ptr _ => w == .w64
  | .bool => true
  | _ => false

@[rule_sem] theorem tyOtherInt_int (w w' : Width) : tyOtherInt (Ty.int w') w = (w' != w) := rfl
@[rule_sem] theorem tyOtherInt_bool (w : Width) : tyOtherInt Ty.bool w = true := rfl
@[rule_sem] theorem tyOtherInt_ptr (w : Width) (e : Option Nat) :
    tyOtherInt (Ty.ptr e) w = (w == .w64) := rfl

@[rule_sem] theorem retype_int_same (w : Width) (x : BitVec w.bits) :
    (Val.int w x).retype (.int w) = .int w x := by
  simp [Val.retype, BitVec.setWidth_eq]

@[rule_sem] theorem retype_bool (t : Ty) (b : Bool) : (Val.bool b).retype t = .bool b := by
  cases t <;> rfl

@[rule_sem] theorem retype_poison (t : Ty) : Val.poison.retype t = .poison := by
  cases t <;> rfl

@[rule_sem] theorem retype_tuple (t : Ty) (vs : List Val) :
    (Val.tuple vs).retype t = match t with | .bool => .poison | _ => .tuple vs := by
  cases t <;> rfl

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
  | bool => cases w <;> rfl
  | _ => simp [Val.retype, tyOtherInt]

@[rule_sem] theorem asBool_retype (t : Ty) (v : Val) :
    (v.retype t).asBool = v.asBool := by
  unfold Val.retype
  split
  · split <;> rfl
  · rfl
  · split <;> rfl
  · rfl
  · cases v <;> simp_all [Val.asBool]
  · rfl

@[rule_sem] theorem hasTy_int (w : Width) (x : BitVec w.bits) (t : Ty) :
    (Val.int w x).hasTy t = true ↔ t = .int w := by
  cases t with
  | int w' => simp only [Val.hasTy, beq_iff_eq, Ty.int.injEq]; exact eq_comm
  | _ => simp [Val.hasTy]

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
shape or a `bool` shape (`poison`), or a pointer shape (`Val.retype`). -/
def retypeNone (t : Ty) (w : Width) : Bool :=
  match t with
  | .int w' => decide (w.bits < w'.bits)
  | .ptr _ => w == .w64
  | .bool => true
  | _ => false

@[rule_sem] theorem retypeNone_int (w w' : Width) :
    retypeNone (.int w') w = decide (w.bits < w'.bits) := rfl
@[rule_sem] theorem retypeNone_bool (w : Width) : retypeNone .bool w = true := rfl
@[rule_sem] theorem retypeNone_ptr (e : Option Nat) (w : Width) :
    retypeNone (.ptr e) w = (w == .w64) := rfl

/-- A retype that keeps a `w`-bit integer an integer of width `w` keeps it an amount. -/
@[rule_sem] theorem retypeNone_of_tyOtherInt {t : Ty} {w : Width} (h : tyOtherInt t w = false) :
    retypeNone t w = false := by
  cases t with
  | int w' =>
    simp only [tyOtherInt, bne_eq_false_iff_eq] at h
    subst h; simp [retypeNone]
  | ptr e => simp only [tyOtherInt] at h; simp [retypeNone, h]
  | bool => simp [tyOtherInt] at h
  | _ => rfl

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
  | _ => simp [Val.retype, retypeNone, Val.asNat]

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

/-! ## `BitVec` shifts by `BitVec` amounts (`rule_bv`: the `bv_decide` fallback of `rule_close`) -/

@[rule_bv] theorem shiftLeft_toNat {w v : Nat} (x : BitVec w) (s : BitVec v) :
    x <<< s.toNat = x <<< s := (BitVec.shiftLeft_eq' (x := x) (y := s)).symm

@[rule_bv] theorem ushiftRight_toNat {w v : Nat} (x : BitVec w) (s : BitVec v) :
    x >>> s.toNat = x >>> s := (BitVec.ushiftRight_eq' (x := x) (y := s)).symm

@[rule_bv] theorem sshiftRight_toNat {w v : Nat} (x : BitVec w) (s : BitVec v) :
    x.sshiftRight s.toNat = x.sshiftRight' s := (BitVec.sshiftRight_eq' (x := x) (y := s)).symm

theorem rotateLeft_toNat {w v : Nat} (x : BitVec w) (s : BitVec v) (hw : 0 < w) (h : w < 2 ^ v) :
    x.rotateLeft s.toNat =
      x <<< (s % BitVec.ofNat v w) ||| x >>> (BitVec.ofNat v w - s % BitVec.ofNat v w) := by
  rw [BitVec.rotateLeft_def, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
  have hm : (s % BitVec.ofNat v w).toNat = s.toNat % w := by
    rw [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  have hs : (BitVec.ofNat v w - s % BitVec.ofNat v w).toNat = w - s.toNat % w := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
    · rw [BitVec.le_def, hm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
      exact Nat.le_of_lt (Nat.mod_lt _ hw)
  rw [hm, hs]

theorem umod_pow2 {v : Nat} (s : BitVec v) (k : Nat) (h : 2 ^ k < 2 ^ v) :
    s % BitVec.ofNat v (2 ^ k) = s &&& BitVec.ofNat v (2 ^ k - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ k - 1 < 2 ^ v := Nat.lt_of_le_of_lt (Nat.sub_le _ _) h
  simp only [BitVec.toNat_umod, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt h1, Nat.and_two_pow_sub_one_eq_mod]

/-- Rotation of a power-of-two width by a `BitVec` amount, as masked shifts. -/
theorem rotateLeft_toNat_pow2 {v : Nat} (k : Nat) (x : BitVec (2 ^ k)) (s : BitVec v)
    (h : 2 ^ k < 2 ^ v) :
    x.rotateLeft s.toNat =
      x <<< (s &&& BitVec.ofNat v (2 ^ k - 1)) |||
        x >>> (BitVec.ofNat v (2 ^ k) - (s &&& BitVec.ofNat v (2 ^ k - 1))) := by
  rw [rotateLeft_toNat x s (Nat.two_pow_pos k) h, umod_pow2 s k h]

@[rule_bv] theorem rotateLeft_toNat8 {v : Nat} (x : BitVec 8) (s : BitVec v) (h : 8 < 2 ^ v) :
    x.rotateLeft s.toNat = x <<< (s &&& BitVec.ofNat v 7) ||| x >>> (BitVec.ofNat v 8 - (s &&& BitVec.ofNat v 7)) :=
  rotateLeft_toNat_pow2 3 x s h
@[rule_bv] theorem rotateLeft_toNat16 {v : Nat} (x : BitVec 16) (s : BitVec v) (h : 16 < 2 ^ v) :
    x.rotateLeft s.toNat = x <<< (s &&& BitVec.ofNat v 15) ||| x >>> (BitVec.ofNat v 16 - (s &&& BitVec.ofNat v 15)) :=
  rotateLeft_toNat_pow2 4 x s h
@[rule_bv] theorem rotateLeft_toNat32 {v : Nat} (x : BitVec 32) (s : BitVec v) (h : 32 < 2 ^ v) :
    x.rotateLeft s.toNat = x <<< (s &&& BitVec.ofNat v 31) ||| x >>> (BitVec.ofNat v 32 - (s &&& BitVec.ofNat v 31)) :=
  rotateLeft_toNat_pow2 5 x s h
@[rule_bv] theorem rotateLeft_toNat64 {v : Nat} (x : BitVec 64) (s : BitVec v) (h : 64 < 2 ^ v) :
    x.rotateLeft s.toNat = x <<< (s &&& BitVec.ofNat v 63) ||| x >>> (BitVec.ofNat v 64 - (s &&& BitVec.ofNat v 63)) :=
  rotateLeft_toNat_pow2 6 x s h

/-- A bound on a `BitVec`'s value as a `BitVec` comparison (`bv_decide` form). -/
@[rule_bv] theorem le_toNat_iff {w : Nat} (n : Nat) (x : BitVec w) (h : n < 2 ^ w) :
    n ≤ x.toNat ↔ BitVec.ofNat w n ≤ x := by
  rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

@[rule_sem] theorem asNat_retype_of_not_other {t : Ty} {w : Width} (x : BitVec w.bits)
    (h : tyOtherInt t w = false) : ((Val.int w x).retype t).asNat = some x.toNat := by
  cases t with
  | int w' =>
    simp only [tyOtherInt, bne_eq_false_iff_eq] at h
    subst h; simp [Val.retype, Val.asNat, BitVec.setWidth_eq]
  | ptr e => cases w <;> first | rfl | cases h
  | bool => cases h
  | _ => rfl

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

end GoFV.Proof.Rules
