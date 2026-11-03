import GoFV.Proof.Low.Rules.Cmp

/-!
# Lowering rule lemmas: shifts (`ARM64.rules:152-179`)

* `(Lsh64x<a> x y) && shiftIsBounded(v) => (SLL x y)` and the `SRA`/`SRL` forms (152, 159, 166):
  a bounded shift's amount is below 64, so the register shift's amount modulo 64 is the amount
  (`refines_shiftB`);
* `(Lsh64x16 [b] x y) && !shiftIsBounded(v) => (Lsh64x32 [b] x (ZeroExt16to32 y))` and the
  8-bit and `Rsh` forms (171, 175, 179): the zero-extended amount has the same value
  (`refines_shiftZ`);
* `(Rsh32x<a> [b] x y) => (Rsh64x<a> [b] (SignExt32to64 x) y)` and the 16/8-bit and unsigned
  (`ZeroExt`) forms (155-157, 162-164): the low bits of the wide shift of the extension are the
  narrow shift at every amount (`sshr_signExtend`, `ushr_setWidth`, `refines_shiftExt`).

Not proven: the ellipsis rules `(Lsh{8,16,32}x<a> ...) => (Lsh64x<a> ...)` (148-150) are false
under Phase 1's semantics (`Lsh64x<a>` asks for a 64-bit operand: on the `int8` value 1 shifted by
0, `Lsh8x64` gives 1 and `Lsh64x64` `poison`); the `CSEL` forms 169, 170, 173, 174, 177, 178 build
`CSEL [OpARM64LessThanU]`, whose auxint the obligation takes from the oracle (`nodeDenL`:
`toAuxIntD .CCop` of `DV.op` is `none`), so they cannot be proven under the current contract.
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

private theorem toNat_setWidth_of_le {n m : Nat} (s : BitVec n) (h : n ≤ m) :
    (s.setWidth m).toNat = s.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by decide) h))

private theorem width_le64 (w : Width) : w.bits ≤ 64 := by cases w <;> decide

/-- A bounded 64-bit shift (`shiftIsBounded`, auxint 1) by an amount of any width as the arm64
register shift (`SLL`/`SRL`/`SRA`: the amount modulo 64, which is below 64). -/
theorem refines_shiftB (a : Width) (f : BitVec 64 → Nat → BitVec 64) (k : Int64) (hk : k = 1)
    (A B : Val) :
    Refines (Val.retypeL (.int .w64) ((Val.asInt .w64 A).elim Val.poison fun x =>
        (Val.asInt a B).elim Val.poison fun s =>
        if (k == 1 && decide (64 ≤ s.toNat)) = true then Val.poison else Val.int .w64 (f x s.toNat)))
      ((Arm64.op2 (.int .w64) (fun x y => f x (y.toNat % 64)) [A, B]).retypeL (.int .w64)) := by
  subst hk
  rcases asInt_cases .w64 A with ha | ⟨x, rfl⟩
  · simp only [ha, Option.elim, retypeL_poison]; exact .poison _
  rcases asInt_cases a B with hb | ⟨s, rfl⟩
  · simp only [hb, Val.asInt_int, Option.elim, retypeL_poison]; exact .poison _
  simp only [Val.asInt_int, Option.elim]
  by_cases hs : 64 ≤ s.toNat
  · simp only [hs, decide_true, Bool.and_true, beq_self_eq_true, ite_true, retypeL_poison]
    exact .poison _
  · have e : (s.setWidth 64).toNat % 64 = s.toNat := by
      rw [toNat_setWidth_of_le s (width_le64 a)]; omega
    simp only [hs, decide_false, Bool.and_false, Bool.false_eq_true, ite_false, Arm64.op2,
      Arm64.reg, setWidth_w64, e, retypeL_res_int, retypeL_int_self]
    exact Refines.refl _

/-- An unbounded 64-bit shift by an 8- or 16-bit amount as the same shift by its zero-extension to
32 bits (`ARM64.rules:171/175/179`). -/
theorem refines_shiftZ (a : Width) (ha : a.bits ≤ 32) (f : BitVec 64 → Nat → BitVec 64) (k : Int64)
    (hk : k = 0) (A B : Val) :
    Refines (Val.retypeL (.int .w64) ((Val.asInt .w64 A).elim Val.poison fun x =>
        (Val.asInt a B).elim Val.poison fun s =>
        if (k == 1 && decide (64 ≤ s.toNat)) = true then Val.poison else Val.int .w64 (f x s.toNat)))
      (Val.retypeL (.int .w64) ((Val.asInt .w64 A).elim Val.poison fun x =>
        (Val.asInt .w32 (Val.retypeL (.int .w32) ((Val.asInt a B).elim Val.poison fun x =>
          Val.int .w32 (BitVec.setWidth 32 x)))).elim Val.poison fun s =>
        if ((if ¬k = 0 then (1 : Int64) else 0) == 1 && decide (64 ≤ s.toNat)) = true then Val.poison
        else Val.int .w64 (f x s.toNat))) := by
  subst hk
  rcases asInt_cases .w64 A with ha' | ⟨x, rfl⟩
  · simp only [ha', Option.elim, retypeL_poison]; exact .poison _
  rcases asInt_cases a B with hb | ⟨s, rfl⟩
  · simp only [hb, Val.asInt_int, Option.elim, retypeL_poison]; exact .poison _
  have e : (s.setWidth 32).toNat = s.toNat := toNat_setWidth_of_le s ha
  simp (config := { decide := true }) only [Val.asInt_int, Option.elim, retypeL_int_self, e,
    ite_false]
  exact Refines.refl _

/-- A narrow shift (`w`-bit value, bounded or not) as the 64-bit shift of its extension `E`, read
back at `w` bits (`hf`: the low `w` bits of the wide shift are the narrow one at every amount;
`ARM64.rules:155-164`). -/
theorem refines_shiftExt (wx a : Width) (E : BitVec wx.bits → BitVec 64)
    (f64 : BitVec 64 → Nat → BitVec 64) (fx : BitVec wx.bits → Nat → BitVec wx.bits)
    (hf : ∀ x n, (f64 (E x) n).setWidth wx.bits = fx x n) (k : Int64) (hk : k = 0 ∨ k = 1)
    (A B : Val) :
    Refines (Val.retypeL (.int wx) ((Val.asInt wx A).elim Val.poison fun x =>
        (Val.asInt a B).elim Val.poison fun s =>
        if (k == 1 && decide (wx.bits ≤ s.toNat)) = true then Val.poison
        else Val.int wx (fx x s.toNat)))
      (Val.retypeL (.int wx) ((Val.asInt .w64 (Val.retypeL (.int .w64)
          ((Val.asInt wx A).elim Val.poison fun x => Val.int .w64 (E x)))).elim Val.poison fun x =>
        (Val.asInt a B).elim Val.poison fun s =>
        if ((if ¬k = 0 then (1 : Int64) else 0) == 1 && decide (64 ≤ s.toNat)) = true then Val.poison
        else Val.int .w64 (f64 x s.toNat))) := by
  rcases asInt_cases wx A with ha | ⟨x, rfl⟩
  · simp only [ha, Option.elim, retypeL_poison]; exact .poison _
  rcases asInt_cases a B with hb | ⟨s, rfl⟩
  · simp only [hb, Val.asInt_int, Option.elim, retypeL_poison, retypeL_int_self]
    exact .poison _
  have hw : wx.bits ≤ Width.w64.bits := width_le64 wx
  have h11 : ((1 : Int64) == 1) = true := by decide
  have h10 : ¬ (1 : Int64) = 0 := by decide
  simp only [Val.asInt_int, Option.elim, retypeL_int_self]
  rcases hk with rfl | rfl
  · simp (config := { decide := true }) only [ite_false, Bool.and_eq_true, false_and, retypeL_int_int .w64 wx _ hw, retypeL_int_self, hf]
    exact Refines.refl _
  · by_cases hs : wx.bits ≤ s.toNat
    · simp only [hs, h11, decide_true, Bool.and_true, ite_true, retypeL_poison]
      exact .poison _
    · have hs' : ¬ 64 ≤ s.toNat := by have := width_le64 wx; omega
      simp only [hs, hs', h10, decide_false, Bool.and_false, Bool.false_eq_true, ite_false,
        not_false_eq_true, ite_true, retypeL_int_int .w64 wx _ hw, retypeL_int_self, hf]
      exact Refines.refl _

/-- The low `w` bits of the logical right shift of a zero-extension. -/
theorem ushr_setWidth {w : Nat} (h : w ≤ 64) (x : BitVec w) (n : Nat) :
    ((x.setWidth 64) >>> n).setWidth w = x >>> n := by
  apply BitVec.eq_of_toNat_eq
  have hx : x.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt hx]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt)

/-- The low `w` bits of the arithmetic right shift of a sign extension. -/
theorem sshr_signExtend {w : Nat} (h : w ≤ 64) (x : BitVec w) (n : Nat) :
    ((x.signExtend 64).sshiftRight n).setWidth w = x.sshiftRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend,
    BitVec.msb_signExtend]
  have h64 : ¬ 64 ≤ i := by omega
  by_cases h1 : n + i < 64 <;> by_cases h2 : n + i < w <;>
    simp only [hi, h64, h1, h2, decide_true, decide_false, Bool.true_and, Bool.not_false,
      ite_true, ite_false, show ¬ w ≤ i by omega, show 0 < 64 by decide]
  · omega
  · split
    · rw [show w - 64 = 0 by omega]; rfl
    · rfl

/-- `ARM64.rules:152`: `(Lsh64x16 <t> x y) && shiftIsBounded(v) => (SLL <t> x y)` -/
theorem r_ARM64_152_sound : ArmRule.Checked r_ARM64_152 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h
  · exact absurd h hcond
  · exact refines_shiftB .w16 (fun x n => x <<< n) _ h _ _

/-- `ARM64.rules:152`: `(Lsh64x32 <t> x y) && shiftIsBounded(v) => (SLL <t> x y)` -/
theorem r_ARM64_152_2_sound : ArmRule.Checked r_ARM64_152_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h
  · exact absurd h hcond
  · exact refines_shiftB .w32 (fun x n => x <<< n) _ h _ _

/-- `ARM64.rules:152`: `(Lsh64x64 <t> x y) && shiftIsBounded(v) => (SLL <t> x y)` -/
theorem r_ARM64_152_3_sound : ArmRule.Checked r_ARM64_152_3 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h
  · exact absurd h hcond
  · exact refines_shiftB .w64 (fun x n => x <<< n) _ h _ _

/-- `ARM64.rules:152`: `(Lsh64x8 <t> x y) && shiftIsBounded(v) => (SLL <t> x y)` -/
theorem r_ARM64_152_4_sound : ArmRule.Checked r_ARM64_152_4 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h
  · exact absurd h hcond
  · exact refines_shiftB .w8 (fun x n => x <<< n) _ h _ _

/-- `ARM64.rules:159`: `(Rsh64x16 <t> x y) && shiftIsBounded(v) => (SRA <t> x y)` -/
theorem r_ARM64_159_sound : ArmRule.Checked r_ARM64_159 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h
  · exact absurd h hcond
  · exact refines_shiftB .w16 (fun x n => x.sshiftRight n) _ h _ _

/-- `ARM64.rules:159`: `(Rsh64x32 <t> x y) && shiftIsBounded(v) => (SRA <t> x y)` -/
theorem r_ARM64_159_2_sound : ArmRule.Checked r_ARM64_159_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h
  · exact absurd h hcond
  · exact refines_shiftB .w32 (fun x n => x.sshiftRight n) _ h _ _

/-- `ARM64.rules:159`: `(Rsh64x64 <t> x y) && shiftIsBounded(v) => (SRA <t> x y)` -/
theorem r_ARM64_159_3_sound : ArmRule.Checked r_ARM64_159_3 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h
  · exact absurd h hcond
  · exact refines_shiftB .w64 (fun x n => x.sshiftRight n) _ h _ _

/-- `ARM64.rules:159`: `(Rsh64x8 <t> x y) && shiftIsBounded(v) => (SRA <t> x y)` -/
theorem r_ARM64_159_4_sound : ArmRule.Checked r_ARM64_159_4 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h
  · exact absurd h hcond
  · exact refines_shiftB .w8 (fun x n => x.sshiftRight n) _ h _ _

/-- `ARM64.rules:166`: `(Rsh64Ux16 <t> x y) && shiftIsBounded(v) => (SRL <t> x y)` -/
theorem r_ARM64_166_sound : ArmRule.Checked r_ARM64_166 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h
  · exact absurd h hcond
  · exact refines_shiftB .w16 (fun x n => x >>> n) _ h _ _

/-- `ARM64.rules:166`: `(Rsh64Ux32 <t> x y) && shiftIsBounded(v) => (SRL <t> x y)` -/
theorem r_ARM64_166_2_sound : ArmRule.Checked r_ARM64_166_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h
  · exact absurd h hcond
  · exact refines_shiftB .w32 (fun x n => x >>> n) _ h _ _

/-- `ARM64.rules:166`: `(Rsh64Ux64 <t> x y) && shiftIsBounded(v) => (SRL <t> x y)` -/
theorem r_ARM64_166_3_sound : ArmRule.Checked r_ARM64_166_3 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h
  · exact absurd h hcond
  · exact refines_shiftB .w64 (fun x n => x >>> n) _ h _ _

/-- `ARM64.rules:166`: `(Rsh64Ux8 <t> x y) && shiftIsBounded(v) => (SRL <t> x y)` -/
theorem r_ARM64_166_4_sound : ArmRule.Checked r_ARM64_166_4 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h
  · exact absurd h hcond
  · exact refines_shiftB .w8 (fun x n => x >>> n) _ h _ _

/-- `ARM64.rules:171`: `(Lsh64x16 <t> [bounded] x y) && !shiftIsBounded(v) => (Lsh64x32 <t> [bounded] x (ZeroExt16to32 y))` -/
theorem r_ARM64_171_sound : ArmRule.Checked r_ARM64_171 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  have hk : e.auxInt [] = 0 := by simpa using hcond
  exact refines_shiftZ .w16 (by decide) (fun x n => x <<< n) _ hk _ _

/-- `ARM64.rules:171`: `(Lsh64x8 <t> [bounded] x y) && !shiftIsBounded(v) => (Lsh64x32 <t> [bounded] x (ZeroExt8to32 y))` -/
theorem r_ARM64_171_2_sound : ArmRule.Checked r_ARM64_171_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  have hk : e.auxInt [] = 0 := by simpa using hcond
  exact refines_shiftZ .w8 (by decide) (fun x n => x <<< n) _ hk _ _

/-- `ARM64.rules:175`: `(Rsh64Ux16 <t> [bounded] x y) && !shiftIsBounded(v) => (Rsh64Ux32 <t> [bounded] x (ZeroExt16to32 y))` -/
theorem r_ARM64_175_sound : ArmRule.Checked r_ARM64_175 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  have hk : e.auxInt [] = 0 := by simpa using hcond
  exact refines_shiftZ .w16 (by decide) (fun x n => x >>> n) _ hk _ _

/-- `ARM64.rules:175`: `(Rsh64Ux8 <t> [bounded] x y) && !shiftIsBounded(v) => (Rsh64Ux32 <t> [bounded] x (ZeroExt8to32 y))` -/
theorem r_ARM64_175_2_sound : ArmRule.Checked r_ARM64_175_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  have hk : e.auxInt [] = 0 := by simpa using hcond
  exact refines_shiftZ .w8 (by decide) (fun x n => x >>> n) _ hk _ _

/-- `ARM64.rules:179`: `(Rsh64x16 <t> [bounded] x y) && !shiftIsBounded(v) => (Rsh64x32 <t> [bounded] x (ZeroExt16to32 y))` -/
theorem r_ARM64_179_sound : ArmRule.Checked r_ARM64_179 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  have hk : e.auxInt [] = 0 := by simpa using hcond
  exact refines_shiftZ .w16 (by decide) (fun x n => x.sshiftRight n) _ hk _ _

/-- `ARM64.rules:179`: `(Rsh64x8 <t> [bounded] x y) && !shiftIsBounded(v) => (Rsh64x32 <t> [bounded] x (ZeroExt8to32 y))` -/
theorem r_ARM64_179_2_sound : ArmRule.Checked r_ARM64_179_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  have hk : e.auxInt [] = 0 := by simpa using hcond
  exact refines_shiftZ .w8 (by decide) (fun x n => x.sshiftRight n) _ hk _ _

/-- `ARM64.rules:155`: `(Rsh32x16 <t> [bounded] x y) => (Rsh64x16 <t> [bounded] (SignExt32to64 x) y)` -/
theorem r_ARM64_155_sound : ArmRule.Checked r_ARM64_155 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w32 .w16 (fun x => x.signExtend 64) (fun x n => x.sshiftRight n) (fun x n => x.sshiftRight n)
    (fun x n => sshr_signExtend (by decide) x n) _ hwf _ _

/-- `ARM64.rules:155`: `(Rsh32x32 <t> [bounded] x y) => (Rsh64x32 <t> [bounded] (SignExt32to64 x) y)` -/
theorem r_ARM64_155_2_sound : ArmRule.Checked r_ARM64_155_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w32 .w32 (fun x => x.signExtend 64) (fun x n => x.sshiftRight n) (fun x n => x.sshiftRight n)
    (fun x n => sshr_signExtend (by decide) x n) _ hwf _ _

/-- `ARM64.rules:155`: `(Rsh32x64 <t> [bounded] x y) => (Rsh64x64 <t> [bounded] (SignExt32to64 x) y)` -/
theorem r_ARM64_155_3_sound : ArmRule.Checked r_ARM64_155_3 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w32 .w64 (fun x => x.signExtend 64) (fun x n => x.sshiftRight n) (fun x n => x.sshiftRight n)
    (fun x n => sshr_signExtend (by decide) x n) _ hwf _ _

/-- `ARM64.rules:155`: `(Rsh32x8 <t> [bounded] x y) => (Rsh64x8 <t> [bounded] (SignExt32to64 x) y)` -/
theorem r_ARM64_155_4_sound : ArmRule.Checked r_ARM64_155_4 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w32 .w8 (fun x => x.signExtend 64) (fun x n => x.sshiftRight n) (fun x n => x.sshiftRight n)
    (fun x n => sshr_signExtend (by decide) x n) _ hwf _ _

/-- `ARM64.rules:156`: `(Rsh16x16 <t> [bounded] x y) => (Rsh64x16 <t> [bounded] (SignExt16to64 x) y)` -/
theorem r_ARM64_156_sound : ArmRule.Checked r_ARM64_156 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w16 .w16 (fun x => x.signExtend 64) (fun x n => x.sshiftRight n) (fun x n => x.sshiftRight n)
    (fun x n => sshr_signExtend (by decide) x n) _ hwf _ _

/-- `ARM64.rules:156`: `(Rsh16x32 <t> [bounded] x y) => (Rsh64x32 <t> [bounded] (SignExt16to64 x) y)` -/
theorem r_ARM64_156_2_sound : ArmRule.Checked r_ARM64_156_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w16 .w32 (fun x => x.signExtend 64) (fun x n => x.sshiftRight n) (fun x n => x.sshiftRight n)
    (fun x n => sshr_signExtend (by decide) x n) _ hwf _ _

/-- `ARM64.rules:156`: `(Rsh16x64 <t> [bounded] x y) => (Rsh64x64 <t> [bounded] (SignExt16to64 x) y)` -/
theorem r_ARM64_156_3_sound : ArmRule.Checked r_ARM64_156_3 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w16 .w64 (fun x => x.signExtend 64) (fun x n => x.sshiftRight n) (fun x n => x.sshiftRight n)
    (fun x n => sshr_signExtend (by decide) x n) _ hwf _ _

/-- `ARM64.rules:156`: `(Rsh16x8 <t> [bounded] x y) => (Rsh64x8 <t> [bounded] (SignExt16to64 x) y)` -/
theorem r_ARM64_156_4_sound : ArmRule.Checked r_ARM64_156_4 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w16 .w8 (fun x => x.signExtend 64) (fun x n => x.sshiftRight n) (fun x n => x.sshiftRight n)
    (fun x n => sshr_signExtend (by decide) x n) _ hwf _ _

/-- `ARM64.rules:157`: `(Rsh8x16 <t> [bounded] x y) => (Rsh64x16 <t> [bounded] (SignExt8to64 x) y)` -/
theorem r_ARM64_157_sound : ArmRule.Checked r_ARM64_157 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w8 .w16 (fun x => x.signExtend 64) (fun x n => x.sshiftRight n) (fun x n => x.sshiftRight n)
    (fun x n => sshr_signExtend (by decide) x n) _ hwf _ _

/-- `ARM64.rules:157`: `(Rsh8x32 <t> [bounded] x y) => (Rsh64x32 <t> [bounded] (SignExt8to64 x) y)` -/
theorem r_ARM64_157_2_sound : ArmRule.Checked r_ARM64_157_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w8 .w32 (fun x => x.signExtend 64) (fun x n => x.sshiftRight n) (fun x n => x.sshiftRight n)
    (fun x n => sshr_signExtend (by decide) x n) _ hwf _ _

/-- `ARM64.rules:157`: `(Rsh8x64 <t> [bounded] x y) => (Rsh64x64 <t> [bounded] (SignExt8to64 x) y)` -/
theorem r_ARM64_157_3_sound : ArmRule.Checked r_ARM64_157_3 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w8 .w64 (fun x => x.signExtend 64) (fun x n => x.sshiftRight n) (fun x n => x.sshiftRight n)
    (fun x n => sshr_signExtend (by decide) x n) _ hwf _ _

/-- `ARM64.rules:157`: `(Rsh8x8 <t> [bounded] x y) => (Rsh64x8 <t> [bounded] (SignExt8to64 x) y)` -/
theorem r_ARM64_157_4_sound : ArmRule.Checked r_ARM64_157_4 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w8 .w8 (fun x => x.signExtend 64) (fun x n => x.sshiftRight n) (fun x n => x.sshiftRight n)
    (fun x n => sshr_signExtend (by decide) x n) _ hwf _ _

/-- `ARM64.rules:162`: `(Rsh32Ux16 <t> [bounded] x y) => (Rsh64Ux16 <t> [bounded] (ZeroExt32to64 x) y)` -/
theorem r_ARM64_162_sound : ArmRule.Checked r_ARM64_162 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w32 .w16 (fun x => x.setWidth 64) (fun x n => x >>> n) (fun x n => x >>> n)
    (fun x n => ushr_setWidth (by decide) x n) _ hwf _ _

/-- `ARM64.rules:162`: `(Rsh32Ux32 <t> [bounded] x y) => (Rsh64Ux32 <t> [bounded] (ZeroExt32to64 x) y)` -/
theorem r_ARM64_162_2_sound : ArmRule.Checked r_ARM64_162_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w32 .w32 (fun x => x.setWidth 64) (fun x n => x >>> n) (fun x n => x >>> n)
    (fun x n => ushr_setWidth (by decide) x n) _ hwf _ _

/-- `ARM64.rules:162`: `(Rsh32Ux64 <t> [bounded] x y) => (Rsh64Ux64 <t> [bounded] (ZeroExt32to64 x) y)` -/
theorem r_ARM64_162_3_sound : ArmRule.Checked r_ARM64_162_3 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w32 .w64 (fun x => x.setWidth 64) (fun x n => x >>> n) (fun x n => x >>> n)
    (fun x n => ushr_setWidth (by decide) x n) _ hwf _ _

/-- `ARM64.rules:162`: `(Rsh32Ux8 <t> [bounded] x y) => (Rsh64Ux8 <t> [bounded] (ZeroExt32to64 x) y)` -/
theorem r_ARM64_162_4_sound : ArmRule.Checked r_ARM64_162_4 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w32 .w8 (fun x => x.setWidth 64) (fun x n => x >>> n) (fun x n => x >>> n)
    (fun x n => ushr_setWidth (by decide) x n) _ hwf _ _

/-- `ARM64.rules:163`: `(Rsh16Ux16 <t> [bounded] x y) => (Rsh64Ux16 <t> [bounded] (ZeroExt16to64 x) y)` -/
theorem r_ARM64_163_sound : ArmRule.Checked r_ARM64_163 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w16 .w16 (fun x => x.setWidth 64) (fun x n => x >>> n) (fun x n => x >>> n)
    (fun x n => ushr_setWidth (by decide) x n) _ hwf _ _

/-- `ARM64.rules:163`: `(Rsh16Ux32 <t> [bounded] x y) => (Rsh64Ux32 <t> [bounded] (ZeroExt16to64 x) y)` -/
theorem r_ARM64_163_2_sound : ArmRule.Checked r_ARM64_163_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w16 .w32 (fun x => x.setWidth 64) (fun x n => x >>> n) (fun x n => x >>> n)
    (fun x n => ushr_setWidth (by decide) x n) _ hwf _ _

/-- `ARM64.rules:163`: `(Rsh16Ux64 <t> [bounded] x y) => (Rsh64Ux64 <t> [bounded] (ZeroExt16to64 x) y)` -/
theorem r_ARM64_163_3_sound : ArmRule.Checked r_ARM64_163_3 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w16 .w64 (fun x => x.setWidth 64) (fun x n => x >>> n) (fun x n => x >>> n)
    (fun x n => ushr_setWidth (by decide) x n) _ hwf _ _

/-- `ARM64.rules:163`: `(Rsh16Ux8 <t> [bounded] x y) => (Rsh64Ux8 <t> [bounded] (ZeroExt16to64 x) y)` -/
theorem r_ARM64_163_4_sound : ArmRule.Checked r_ARM64_163_4 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w16 .w8 (fun x => x.setWidth 64) (fun x n => x >>> n) (fun x n => x >>> n)
    (fun x n => ushr_setWidth (by decide) x n) _ hwf _ _

/-- `ARM64.rules:164`: `(Rsh8Ux16 <t> [bounded] x y) => (Rsh64Ux16 <t> [bounded] (ZeroExt8to64 x) y)` -/
theorem r_ARM64_164_sound : ArmRule.Checked r_ARM64_164 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w8 .w16 (fun x => x.setWidth 64) (fun x n => x >>> n) (fun x n => x >>> n)
    (fun x n => ushr_setWidth (by decide) x n) _ hwf _ _

/-- `ARM64.rules:164`: `(Rsh8Ux32 <t> [bounded] x y) => (Rsh64Ux32 <t> [bounded] (ZeroExt8to64 x) y)` -/
theorem r_ARM64_164_2_sound : ArmRule.Checked r_ARM64_164_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w8 .w32 (fun x => x.setWidth 64) (fun x n => x >>> n) (fun x n => x >>> n)
    (fun x n => ushr_setWidth (by decide) x n) _ hwf _ _

/-- `ARM64.rules:164`: `(Rsh8Ux64 <t> [bounded] x y) => (Rsh64Ux64 <t> [bounded] (ZeroExt8to64 x) y)` -/
theorem r_ARM64_164_3_sound : ArmRule.Checked r_ARM64_164_3 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w8 .w64 (fun x => x.setWidth 64) (fun x n => x >>> n) (fun x n => x >>> n)
    (fun x n => ushr_setWidth (by decide) x n) _ hwf _ _

/-- `ARM64.rules:164`: `(Rsh8Ux8 <t> [bounded] x y) => (Rsh64Ux8 <t> [bounded] (ZeroExt8to64 x) y)` -/
theorem r_ARM64_164_4_sound : ArmRule.Checked r_ARM64_164_4 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_shiftExt .w8 .w8 (fun x => x.setWidth 64) (fun x n => x >>> n) (fun x n => x >>> n)
    (fun x n => ushr_setWidth (by decide) x n) _ hwf _ _

end GoFV.Proof.Low.Rules
