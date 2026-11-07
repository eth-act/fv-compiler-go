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

* `(Lsh64x64 <t> x y) && !shiftIsBounded(v) => (CSEL [OpARM64LessThanU] (SLL <t> x y) (Const64 <t>
  [0]) (CMPconst [64] y))` and the `CMPWconst`/`SRL` forms (169, 170, 173, 174): `LO` on the
  compare's flags is `y < 64`, and the shift by 64 or more is 0 (`refines_shiftCsel`); the `SRA`
  forms (177, 178) clamp the amount to 63 (`refines_sraCsel`). The `CCop` auxint
  `[OpARM64LessThanU]` is its Go opcode number (`toAuxIntL`).

The 64-bit shift rules (152, 159, 166, 169-179) hold at every integer shape of the matched value
(`topOKL` admits the 64-bit shifts there, `top64Op`; `divmod.rules` builds `(Rsh64Ux64
<typ.UInt32> …)`): Phase 1's shift and the arm64 register are 64-bit integers, which `retypeL`
reads at the shape's low bits on both sides (`retypeL_int64`).

Not proven: the ellipsis rules `(Lsh{8,16,32}x<a> ...) => (Lsh64x<a> ...)` (148-150) are false
under Phase 1's semantics (`Lsh64x<a>` asks for a 64-bit operand: on the `int8` value 1 shifted by
0, `Lsh8x64` gives 1 and `Lsh64x64` `poison`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

private theorem toNat_setWidth_of_le {n m : Nat} (s : BitVec n) (h : n ≤ m) :
    (s.setWidth m).toNat = s.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by decide) h))

private theorem width_le64 (w : Width) : w.bits ≤ 64 := by cases w <;> decide

/-- A 64-bit integer at an integer shape `.int w` (a 64-bit shift or `Const64` at any integer
shape, `top64Op`): its low `w` bits. -/
theorem retypeL_int64 (w : Width) (x : BitVec 64) :
    (Val.int .w64 x).retypeL (.int w) = .int w (x.setWidth w.bits) :=
  retypeL_int_int .w64 w x (width_le64 w)

/-- A bounded 64-bit shift (`shiftIsBounded`, auxint 1) by an amount of any width as the arm64
register shift (`SLL`/`SRL`/`SRA`: the amount modulo 64, which is below 64), at any integer shape
`.int w` of the result (`top64Op`). -/
theorem refines_shiftB (a w : Width) (f : BitVec 64 → Nat → BitVec 64) (k : Int64) (hk : k = 1)
    (A B : Val) :
    Refines (Val.retypeL (.int w) ((Val.asInt .w64 A).elim Val.poison fun x =>
        (Val.asInt a B).elim Val.poison fun s =>
        if (k == 1 && decide (64 ≤ s.toNat)) = true then Val.poison else Val.int .w64 (f x s.toNat)))
      ((Arm64.op2 (.int w) (fun x y => f x (y.toNat % 64)) [A, B]).retypeL (.int w)) := by
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
      Arm64.reg, setWidth_w64, e, retypeL_res_int, retypeL_int64]
    exact Refines.refl _

/-- An unbounded 64-bit shift by an 8- or 16-bit amount as the same shift by its zero-extension to
32 bits (`ARM64.rules:171/175/179`), at any integer shape `.int w` of the result (`top64Op`). -/
theorem refines_shiftZ (a w : Width) (ha : a.bits ≤ 32) (f : BitVec 64 → Nat → BitVec 64)
    (k : Int64) (hk : k = 0) (A B : Val) :
    Refines (Val.retypeL (.int w) ((Val.asInt .w64 A).elim Val.poison fun x =>
        (Val.asInt a B).elim Val.poison fun s =>
        if (k == 1 && decide (64 ≤ s.toNat)) = true then Val.poison else Val.int .w64 (f x s.toNat)))
      (Val.retypeL (.int w) ((Val.asInt .w64 A).elim Val.poison fun x =>
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
  all_goals
    rcases hwf with h | h
    · exact absurd h hcond
    · exact refines_shiftB .w16 _ (fun x n => x <<< n) _ h _ _

/-- `ARM64.rules:152`: `(Lsh64x32 <t> x y) && shiftIsBounded(v) => (SLL <t> x y)` -/
theorem r_ARM64_152_2_sound : ArmRule.Checked r_ARM64_152_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    rcases hwf with h | h
    · exact absurd h hcond
    · exact refines_shiftB .w32 _ (fun x n => x <<< n) _ h _ _

/-- `ARM64.rules:152`: `(Lsh64x64 <t> x y) && shiftIsBounded(v) => (SLL <t> x y)` -/
theorem r_ARM64_152_3_sound : ArmRule.Checked r_ARM64_152_3 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    rcases hwf with h | h
    · exact absurd h hcond
    · exact refines_shiftB .w64 _ (fun x n => x <<< n) _ h _ _

/-- `ARM64.rules:152`: `(Lsh64x8 <t> x y) && shiftIsBounded(v) => (SLL <t> x y)` -/
theorem r_ARM64_152_4_sound : ArmRule.Checked r_ARM64_152_4 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    rcases hwf with h | h
    · exact absurd h hcond
    · exact refines_shiftB .w8 _ (fun x n => x <<< n) _ h _ _

/-- `ARM64.rules:159`: `(Rsh64x16 <t> x y) && shiftIsBounded(v) => (SRA <t> x y)` -/
theorem r_ARM64_159_sound : ArmRule.Checked r_ARM64_159 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    rcases hwf with h | h
    · exact absurd h hcond
    · exact refines_shiftB .w16 _ (fun x n => x.sshiftRight n) _ h _ _

/-- `ARM64.rules:159`: `(Rsh64x32 <t> x y) && shiftIsBounded(v) => (SRA <t> x y)` -/
theorem r_ARM64_159_2_sound : ArmRule.Checked r_ARM64_159_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    rcases hwf with h | h
    · exact absurd h hcond
    · exact refines_shiftB .w32 _ (fun x n => x.sshiftRight n) _ h _ _

/-- `ARM64.rules:159`: `(Rsh64x64 <t> x y) && shiftIsBounded(v) => (SRA <t> x y)` -/
theorem r_ARM64_159_3_sound : ArmRule.Checked r_ARM64_159_3 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    rcases hwf with h | h
    · exact absurd h hcond
    · exact refines_shiftB .w64 _ (fun x n => x.sshiftRight n) _ h _ _

/-- `ARM64.rules:159`: `(Rsh64x8 <t> x y) && shiftIsBounded(v) => (SRA <t> x y)` -/
theorem r_ARM64_159_4_sound : ArmRule.Checked r_ARM64_159_4 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    rcases hwf with h | h
    · exact absurd h hcond
    · exact refines_shiftB .w8 _ (fun x n => x.sshiftRight n) _ h _ _

/-- `ARM64.rules:166`: `(Rsh64Ux16 <t> x y) && shiftIsBounded(v) => (SRL <t> x y)` -/
theorem r_ARM64_166_sound : ArmRule.Checked r_ARM64_166 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    rcases hwf with h | h
    · exact absurd h hcond
    · exact refines_shiftB .w16 _ (fun x n => x >>> n) _ h _ _

/-- `ARM64.rules:166`: `(Rsh64Ux32 <t> x y) && shiftIsBounded(v) => (SRL <t> x y)` -/
theorem r_ARM64_166_2_sound : ArmRule.Checked r_ARM64_166_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    rcases hwf with h | h
    · exact absurd h hcond
    · exact refines_shiftB .w32 _ (fun x n => x >>> n) _ h _ _

/-- `ARM64.rules:166`: `(Rsh64Ux64 <t> x y) && shiftIsBounded(v) => (SRL <t> x y)` -/
theorem r_ARM64_166_3_sound : ArmRule.Checked r_ARM64_166_3 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    rcases hwf with h | h
    · exact absurd h hcond
    · exact refines_shiftB .w64 _ (fun x n => x >>> n) _ h _ _

/-- `ARM64.rules:166`: `(Rsh64Ux8 <t> x y) && shiftIsBounded(v) => (SRL <t> x y)` -/
theorem r_ARM64_166_4_sound : ArmRule.Checked r_ARM64_166_4 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    rcases hwf with h | h
    · exact absurd h hcond
    · exact refines_shiftB .w8 _ (fun x n => x >>> n) _ h _ _

/-- `ARM64.rules:171`: `(Lsh64x16 <t> [bounded] x y) && !shiftIsBounded(v) => (Lsh64x32 <t> [bounded] x (ZeroExt16to32 y))` -/
theorem r_ARM64_171_sound : ArmRule.Checked r_ARM64_171 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    have hk : e.auxInt [] = 0 := by simpa using hcond
    exact refines_shiftZ .w16 _ (by decide) (fun x n => x <<< n) _ hk _ _

/-- `ARM64.rules:171`: `(Lsh64x8 <t> [bounded] x y) && !shiftIsBounded(v) => (Lsh64x32 <t> [bounded] x (ZeroExt8to32 y))` -/
theorem r_ARM64_171_2_sound : ArmRule.Checked r_ARM64_171_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    have hk : e.auxInt [] = 0 := by simpa using hcond
    exact refines_shiftZ .w8 _ (by decide) (fun x n => x <<< n) _ hk _ _

/-- `ARM64.rules:175`: `(Rsh64Ux16 <t> [bounded] x y) && !shiftIsBounded(v) => (Rsh64Ux32 <t> [bounded] x (ZeroExt16to32 y))` -/
theorem r_ARM64_175_sound : ArmRule.Checked r_ARM64_175 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    have hk : e.auxInt [] = 0 := by simpa using hcond
    exact refines_shiftZ .w16 _ (by decide) (fun x n => x >>> n) _ hk _ _

/-- `ARM64.rules:175`: `(Rsh64Ux8 <t> [bounded] x y) && !shiftIsBounded(v) => (Rsh64Ux32 <t> [bounded] x (ZeroExt8to32 y))` -/
theorem r_ARM64_175_2_sound : ArmRule.Checked r_ARM64_175_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    have hk : e.auxInt [] = 0 := by simpa using hcond
    exact refines_shiftZ .w8 _ (by decide) (fun x n => x >>> n) _ hk _ _

/-- `ARM64.rules:179`: `(Rsh64x16 <t> [bounded] x y) && !shiftIsBounded(v) => (Rsh64x32 <t> [bounded] x (ZeroExt16to32 y))` -/
theorem r_ARM64_179_sound : ArmRule.Checked r_ARM64_179 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    have hk : e.auxInt [] = 0 := by simpa using hcond
    exact refines_shiftZ .w16 _ (by decide) (fun x n => x.sshiftRight n) _ hk _ _

/-- `ARM64.rules:179`: `(Rsh64x8 <t> [bounded] x y) && !shiftIsBounded(v) => (Rsh64x32 <t> [bounded] x (ZeroExt8to32 y))` -/
theorem r_ARM64_179_2_sound : ArmRule.Checked r_ARM64_179_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    have hk : e.auxInt [] = 0 := by simpa using hcond
    exact refines_shiftZ .w8 _ (by decide) (fun x n => x.sshiftRight n) _ hk _ _

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

/-! ## Unbounded shifts by `CSEL` (`ARM64.rules:169-178`) -/

set_option maxRecDepth 100000 in
/-- The `CCop` auxint `OpARM64LessThanU` (its Go opcode number, `toAuxIntL`) is `LO`. -/
theorem ofAux_lessThanU : Cond.ofAux (Int64.ofNat Op.ARM64LessThanU.goNum) = some .lo := by
  rfl

/-- `LO` on the flags of `CMPconst [64] y`: `y < 64` (an integer of at most 64 bits). -/
theorem lo_cmp64 (a : Width) (ha : a.bits ≤ 64) (s : BitVec a.bits) :
    Cond.lo.onVal ((Arm64.cmp (.int a s) (.int .w64 (BitVec.ofInt 64 64))).retypeL .flags) =
      some (decide (s.toNat < 64)) := by
  rw [cmp_int, retypeL_cmpRes, onVal_cmpRes, (cond_sub _ _ (sub_lt64 _ _)).2.2.2.2.1]
  have hs := Nat.lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by decide) ha)
  simp [BitVec.ult, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hs]

/-- `LO` on the flags of `CMPWconst [64] y`: `y < 64` (a 32-bit integer). -/
theorem lo_cmp32 (s : BitVec Width.w32.bits) :
    Cond.lo.onVal ((Arm64.cmp1w (fun x => Arm64.subFlags x (Arm64.imm32 (Int64.ofInt 64)))
      [.int .w32 s]).retypeL .flags) = some (decide (s.toNat < 64)) := by
  simp only [Arm64.cmp1w, Arm64.reg32, Arm64.reg, Option.map_some,
    BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), setWidth_w32, retypeL_cmpRes,
    onVal_cmpRes]
  rw [(cond_sub _ _ (sub_lt32 _ _)).2.2.2.2.1]
  simp [BitVec.ult, Arm64.imm32]

/-- A left shift by 64 or more is 0. -/
theorem shiftLeft_ge (x : BitVec 64) (n : Nat) (h : 64 ≤ n) : x <<< n = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq, Nat.mul_mod, show 2 ^ n % 2 ^ 64 = 0 from
    Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 h)]
  simp

/-- A logical right shift by 64 or more is 0. -/
theorem ushiftRight_ge (x : BitVec 64) (n : Nat) (h : 64 ≤ n) : x >>> n = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod]
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))

/-- An arithmetic right shift by 63 or more is the shift by 63 (all sign bits). -/
theorem sshiftRight_ge (x : BitVec 64) (n : Nat) (h : 63 ≤ n) : x.sshiftRight n = x.sshiftRight 63 := by
  rcases Nat.eq_or_lt_of_le h with rfl | h'
  · rfl
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_sshiftRight]
  have hn : ¬ n + i < 64 := by omega
  by_cases h2 : 63 + i < 64
  · obtain rfl : i = 0 := by omega
    simp [show ¬ n < 64 by omega, BitVec.msb_eq_getLsbD_last]
  · simp [hn, h2]

/-- An unbounded 64-bit shift (`f`: 0 at 64 or more) as `CSEL [LessThanU] (shift x y) 0 (CMP… [64] y)`
(`ARM64.rules:169/170/173/174`; `G`: the flags of the compare, `LO` iff `y < 64`), at any integer
shape `.int w` of the result (`top64Op`; the selected arm's register read back at `w` bits). -/
theorem refines_shiftCsel (a w : Width) (ha : a.bits ≤ 64) (f : BitVec 64 → Nat → BitVec 64)
    (hf : ∀ x n, 64 ≤ n → f x n = 0) (k : Int64) (hk : k = 0) (G : Val → Val)
    (hG : ∀ s : BitVec a.bits, Cond.lo.onVal (G (.int a s)) = some (decide (s.toNat < 64)))
    (A B : Val) :
    Refines (Val.retypeL (.int w) ((Val.asInt .w64 A).elim Val.poison fun x =>
        (Val.asInt a B).elim Val.poison fun s =>
        if (k == 1 && decide (64 ≤ s.toNat)) = true then Val.poison else Val.int .w64 (f x s.toNat)))
      (Val.retypeL (.int w) (Arm64.csel (.int w) (Int64.ofNat Op.ARM64LessThanU.goNum) none
        [Val.retypeL (.int w) (Arm64.op2 (.int w) (fun x y => f x (y.toNat % 64)) [A, B]),
          Val.retypeL (.int w) (Val.i64 (BitVec.ofInt 64 0)), G B])) := by
  subst hk
  rcases asInt_cases .w64 A with h | ⟨x, rfl⟩
  · simp only [h, Option.elim, retypeL_poison]; exact .poison _
  rcases asInt_cases a B with h | ⟨s, rfl⟩
  · simp only [h, Val.asInt_int, Option.elim, retypeL_poison]; exact .poison _
  have hs : (s.setWidth 64).toNat = s.toNat := toNat_setWidth_of_le s ha
  have hb : ∀ v : BitVec w.bits, (v.setWidth 64).setWidth w.bits = v := fun v => by
    rw [BitVec.setWidth_setWidth_of_le _ (width_le64 w), BitVec.setWidth_eq]
  have h01 : ((0 : Int64) == 1) = false := by decide
  simp only [Val.asInt_int, Option.elim, Arm64.csel, Arm64.condOn, ofAux_lessThanU,
    Option.bind_some, hG, Arm64.op2, Arm64.reg, setWidth_w64, retypeL_res_int, Val.i64,
    retypeL_int64, h01, Bool.false_and, Bool.false_eq_true, ite_false]
  by_cases h64 : s.toNat < 64
  · simp only [h64, decide_true, Arm64.regVal, Arm64.reg, Arm64.res, hs, Nat.mod_eq_of_lt h64,
      retypeL_res_int, retypeL_int64, hb, ite_true]
    exact Refines.refl _
  · have h0 : BitVec.ofInt 64 0 = 0 := by decide
    simp only [h64, decide_false, Arm64.regVal, Arm64.reg, Arm64.res, retypeL_res_int,
      retypeL_int64, hb, hf x s.toNat (by omega), h0]
    exact Refines.refl _

/-- An unbounded 64-bit arithmetic right shift as `SRA x (CSEL [LessThanU] <T> y 63 (CMP… [64] y))`
(`ARM64.rules:177/178`): the amount clamped to 63 at the shape `T` of `y`, whose register reads
back (`hT`, `hY`), at any integer shape `.int w` of the result (`top64Op`). -/
theorem refines_sraCsel (a w : Width) (ha : a.bits ≤ 64) (k : Int64) (hk : k = 0) (T : Ty)
    (G : Val → Val)
    (hG : ∀ s : BitVec a.bits, Cond.lo.onVal (G (.int a s)) = some (decide (s.toNat < 64)))
    (hT : ∀ s : BitVec a.bits, Arm64.reg ((Arm64.regVal T (.int a s)).retypeL T) = some (s.setWidth 64))
    (hY : Arm64.reg ((Arm64.regVal T ((Val.i64 (BitVec.ofInt 64 63)).retypeL T)).retypeL T) = some 63)
    (A B : Val) :
    Refines (Val.retypeL (.int w) ((Val.asInt .w64 A).elim Val.poison fun x =>
        (Val.asInt a B).elim Val.poison fun s =>
        if (k == 1 && decide (64 ≤ s.toNat)) = true then Val.poison
        else Val.int .w64 (x.sshiftRight s.toNat)))
      (Val.retypeL (.int w) (Arm64.op2 (.int w) (fun x y => x.sshiftRight (y.toNat % 64))
        [A, Val.retypeL T (Arm64.csel T (Int64.ofNat Op.ARM64LessThanU.goNum) none
          [B, Val.retypeL T (Val.i64 (BitVec.ofInt 64 63)), G B])])) := by
  subst hk
  rcases asInt_cases .w64 A with h | ⟨x, rfl⟩
  · simp only [h, Option.elim, retypeL_poison]; exact .poison _
  rcases asInt_cases a B with h | ⟨s, rfl⟩
  · simp only [h, Val.asInt_int, Option.elim, retypeL_poison]; exact .poison _
  have hs : (s.setWidth 64).toNat = s.toNat := toNat_setWidth_of_le s ha
  have h01 : ((0 : Int64) == 1) = false := by decide
  simp only [Val.asInt_int, Option.elim, Arm64.csel, Arm64.condOn, ofAux_lessThanU,
    Option.bind_some, hG, h01, Bool.false_and, Bool.false_eq_true, ite_false]
  have hx : Arm64.reg (.int .w64 x) = some x := by simp [Arm64.reg]
  by_cases h64 : s.toNat < 64
  · simp only [h64, decide_true, Arm64.op2, hx, hT, setWidth_w64, retypeL_res_int,
      retypeL_int64, BitVec.setWidth_eq, hs, Nat.mod_eq_of_lt h64]
    exact Refines.refl _
  · simp only [h64, decide_false, Arm64.op2, hx, hY, setWidth_w64, retypeL_res_int,
      retypeL_int64, BitVec.setWidth_eq]
    rw [sshiftRight_ge x s.toNat (by omega)]
    exact Refines.refl _

/-- `ARM64.rules:169`: `(Lsh64x64 <t> x y) && !shiftIsBounded(v) => (CSEL [OpARM64LessThanU] (SLL <t> x y) (Const64 <t> [0]) (CMPconst [64] y))` -/
theorem r_ARM64_169_sound : ArmRule.Checked r_ARM64_169 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    have hk : e.auxInt [] = 0 := by simpa using hcond
    exact refines_shiftCsel .w64 _ (by decide) (fun x n => x <<< n) shiftLeft_ge _ hk
      (fun B => Val.retypeL Ty.flags (Arm64.cmp B (Val.int .w64 (BitVec.ofInt 64 64)))) (lo_cmp64 .w64 (by decide)) _ _

/-- `ARM64.rules:170`: `(Lsh64x32 <t> x y) && !shiftIsBounded(v) => (CSEL [OpARM64LessThanU] (SLL <t> x y) (Const64 <t> [0]) (CMPWconst [64] y))` -/
theorem r_ARM64_170_sound : ArmRule.Checked r_ARM64_170 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    have hk : e.auxInt [] = 0 := by simpa using hcond
    exact refines_shiftCsel .w32 _ (by decide) (fun x n => x <<< n) shiftLeft_ge _ hk
      (fun B => Val.retypeL Ty.flags (Arm64.cmp1w (fun x => Arm64.subFlags x (Arm64.imm32 (Int64.ofInt 64))) [B])) lo_cmp32 _ _

/-- `ARM64.rules:173`: `(Rsh64Ux64 <t> x y) && !shiftIsBounded(v) => (CSEL [OpARM64LessThanU] (SRL <t> x y) (Const64 <t> [0]) (CMPconst [64] y))` -/
theorem r_ARM64_173_sound : ArmRule.Checked r_ARM64_173 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    have hk : e.auxInt [] = 0 := by simpa using hcond
    exact refines_shiftCsel .w64 _ (by decide) (fun x n => x >>> n) ushiftRight_ge _ hk
      (fun B => Val.retypeL Ty.flags (Arm64.cmp B (Val.int .w64 (BitVec.ofInt 64 64)))) (lo_cmp64 .w64 (by decide)) _ _

/-- `ARM64.rules:174`: `(Rsh64Ux32 <t> x y) && !shiftIsBounded(v) => (CSEL [OpARM64LessThanU] (SRL <t> x y) (Const64 <t> [0]) (CMPWconst [64] y))` -/
theorem r_ARM64_174_sound : ArmRule.Checked r_ARM64_174 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    have hk : e.auxInt [] = 0 := by simpa using hcond
    exact refines_shiftCsel .w32 _ (by decide) (fun x n => x >>> n) ushiftRight_ge _ hk
      (fun B => Val.retypeL Ty.flags (Arm64.cmp1w (fun x => Arm64.subFlags x (Arm64.imm32 (Int64.ofInt 64))) [B])) lo_cmp32 _ _

/-- `CSEL`'s selected 32-bit input at the 32-bit shape: its zero-extended register. -/
theorem reg_regVal_w32 (s : BitVec Width.w32.bits) :
    Arm64.reg ((Arm64.regVal (.int .w32) (.int .w32 s)).retypeL (.int .w32)) = some (s.setWidth 64) := by
  simp only [Arm64.regVal, Arm64.reg, Arm64.res]
  rw [retypeL_int_int .w64 .w32 _ (by decide)]
  simp only [BitVec.setWidth_setWidth_of_le _ (show Width.w32.bits ≤ 64 by decide)]
  rfl

/-- `ARM64.rules:177`: `(Rsh64x64 <t> x y) && !shiftIsBounded(v) => (SRA x (CSEL [OpARM64LessThanU] <y.Type> y (Const64 <y.Type> [63]) (CMPconst [64] y)))` -/
theorem r_ARM64_177_sound : ArmRule.Checked r_ARM64_177 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    have hk : e.auxInt [] = 0 := by simpa using hcond
    have hT := hty.2
    generalize e.ty [1] = T at hT ⊢
    generalize e.leaf [1] = B at hT ⊢
    rcases asInt_cases .w64 B with hB | ⟨s, rfl⟩
    · rcases asInt_cases .w64 (e.leaf [0]) with h0 | ⟨x, h0⟩ <;>
        simp only [h0, hB, Val.asInt_int, Option.elim, retypeL_poison] <;> exact .poison _
    cases T <;> simp [Val.hasTy] at hT
    all_goals first
      | (subst hT; exact refines_sraCsel .w64 _ (by decide) _ hk _ (fun B => Val.retypeL Ty.flags (Arm64.cmp B (Val.int .w64 (BitVec.ofInt 64 64)))) (lo_cmp64 .w64 (by decide))
          (fun s => by simp [Arm64.regVal, Arm64.reg, Arm64.res, Val.retypeL, Val.widen, Val.retype])
          rfl _ _)
      | exact refines_sraCsel .w64 _ (by decide) _ hk _ (fun B => Val.retypeL Ty.flags (Arm64.cmp B (Val.int .w64 (BitVec.ofInt 64 64)))) (lo_cmp64 .w64 (by decide))
          (fun s => by simp [Arm64.regVal, Arm64.reg, Arm64.res, Val.retypeL, Val.widen, Val.retype])
          rfl _ _

/-- `ARM64.rules:178`: `(Rsh64x32 <t> x y) && !shiftIsBounded(v) => (SRA x (CSEL [OpARM64LessThanU] <y.Type> y (Const64 <y.Type> [63]) (CMPWconst [64] y)))` -/
theorem r_ARM64_178_sound : ArmRule.Checked r_ARM64_178 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals
    have hk : e.auxInt [] = 0 := by simpa using hcond
    have hT := hty.2
    generalize e.ty [1] = T at hT ⊢
    generalize e.leaf [1] = B at hT ⊢
    rcases asInt_cases .w32 B with hB | ⟨s, rfl⟩
    · rcases asInt_cases .w64 (e.leaf [0]) with h0 | ⟨x, h0⟩ <;>
        simp only [h0, hB, Val.asInt_int, Option.elim, retypeL_poison] <;> exact .poison _
    cases T <;> simp [Val.hasTy] at hT
    subst hT
    exact refines_sraCsel .w32 _ (by decide) _ hk _ (fun B => Val.retypeL Ty.flags
      (Arm64.cmp1w (fun x => Arm64.subFlags x (Arm64.imm32 (Int64.ofInt 64))) [B])) lo_cmp32
      reg_regVal_w32 rfl _ _

end GoFV.Proof.Low.Rules
