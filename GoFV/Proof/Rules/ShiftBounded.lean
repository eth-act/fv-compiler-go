import GoFV.Proof.Rules.NonVacuous
import GoFV.Proof.Rules.SoundW
import GoFV.Proof.ValRefine
import GoFV.Rules.Generated.Generic.Values05
import GoFV.Rules.Generated.Generic.Values06
import GoFV.Rules.Generated.Generic.Values10
import GoFV.Rules.Generated.Generic.Values11

/-!
# Rule lemmas: the bounded-shift rules `generic.rules:1188–1198`

`(Rsh64x16 [false] x con:(Const16 [c])) && 0 < c && c < 64 => (Rsh64x16 [true] x con)` and its
siblings only set the `bounded` flag of a shift whose amount is in range. The divmod rules build
such shifts at the dividend's type (`int32` for an `Rsh64x16`), so the matched value can be
narrower than its op; the checker accepts these rules at any top type (`anyTop`) and their
obligation is `Rule.SoundW` (`SoundW.lean`): the retyped values agree. `rule_auto_w` is
`rule_auto` for `Rule.SoundWP`: the same unfolding without the shape premise, then
`retype_mono` and `rule_auto`'s case splits and closers.
-/

namespace GoFV.Proof.Rules

open Lean Elab Tactic GoFV.SSA GoFV.SSA.Sem

set_option hygiene false in
/-- `rule_unfold` and the rest of `rule_auto` for a goal `Rule.SoundWP r` (`r` a constant whose
condition does not call `isNonNegative`). -/
elab "rule_auto_w" : tactic => do
  let ty ← instantiateMVars (← getMainTarget)
  let some r := ty.getAppArgs[0]? | throwError "rule_auto_w: goal is not `Rule.SoundWP r`"
  let some rn := r.constName? | throwError "rule_auto_w: rule is not a constant"
  let rid := mkIdent rn
  evalTactic (← `(tactic| (
    refine ⟨rfl, ?_⟩
    intro e or hbt
    dsimp only [$rid:ident, rule_unfold_ds]
    simp only [rule_helper, rule_unfold_s]
    intro hwf hc hcond hlt hat hnn
    clear hat hnn
    (try dsimp only [GoFV.Proof.Rules.condHolds, rule_unfold_ds] at hcond)
    (try simp only [rule_helper, rule_unfold_s] at hcond)
    rule_oracle_bool
    rule_cond_bool
    apply retype_mono
    (try rule_ands)
    (try rule_clear_oracle)
    (try rule_norm)
    (try rule_ands)
    all_goals (repeat rule_split1)
    all_goals (try rule_widths)
    all_goals rule_close)))

/-- `generic.rules:1188`: `(Lsh64x16 [false] x con:(Const16 [c])) && 0 < c && c < 64 => (Lsh64x16 [true] x con)` -/
theorem r_generic_1188_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1188 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1188`: `(Lsh64x32 [false] x con:(Const32 [c])) && 0 < c && c < 64 => (Lsh64x32 [true] x con)` -/
theorem r_generic_1188_2_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1188_2 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1188`: `(Lsh64x64 [false] x con:(Const64 [c])) && 0 < c && c < 64 => (Lsh64x64 [true] x con)` -/
theorem r_generic_1188_3_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1188_3 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1188`: `(Lsh64x8 [false] x con:(Const8 [c])) && 0 < c && c < 64 => (Lsh64x8 [true] x con)` -/
theorem r_generic_1188_4_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1188_4 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1189`: `(Rsh64x16 [false] x con:(Const16 [c])) && 0 < c && c < 64 => (Rsh64x16 [true] x con)` -/
theorem r_generic_1189_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1189 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1189`: `(Rsh64x32 [false] x con:(Const32 [c])) && 0 < c && c < 64 => (Rsh64x32 [true] x con)` -/
theorem r_generic_1189_2_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1189_2 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1189`: `(Rsh64x64 [false] x con:(Const64 [c])) && 0 < c && c < 64 => (Rsh64x64 [true] x con)` -/
theorem r_generic_1189_3_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1189_3 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1189`: `(Rsh64x8 [false] x con:(Const8 [c])) && 0 < c && c < 64 => (Rsh64x8 [true] x con)` -/
theorem r_generic_1189_4_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1189_4 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1190`: `(Rsh64Ux16 [false] x con:(Const16 [c])) && 0 < c && c < 64 => (Rsh64Ux16 [true] x con)` -/
theorem r_generic_1190_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1190 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1190`: `(Rsh64Ux32 [false] x con:(Const32 [c])) && 0 < c && c < 64 => (Rsh64Ux32 [true] x con)` -/
theorem r_generic_1190_2_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1190_2 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1190`: `(Rsh64Ux64 [false] x con:(Const64 [c])) && 0 < c && c < 64 => (Rsh64Ux64 [true] x con)` -/
theorem r_generic_1190_3_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1190_3 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1190`: `(Rsh64Ux8 [false] x con:(Const8 [c])) && 0 < c && c < 64 => (Rsh64Ux8 [true] x con)` -/
theorem r_generic_1190_4_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1190_4 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1191`: `(Lsh32x16 [false] x con:(Const16 [c])) && 0 < c && c < 32 => (Lsh32x16 [true] x con)` -/
theorem r_generic_1191_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1191 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1191`: `(Lsh32x32 [false] x con:(Const32 [c])) && 0 < c && c < 32 => (Lsh32x32 [true] x con)` -/
theorem r_generic_1191_2_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1191_2 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1191`: `(Lsh32x64 [false] x con:(Const64 [c])) && 0 < c && c < 32 => (Lsh32x64 [true] x con)` -/
theorem r_generic_1191_3_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1191_3 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1191`: `(Lsh32x8 [false] x con:(Const8 [c])) && 0 < c && c < 32 => (Lsh32x8 [true] x con)` -/
theorem r_generic_1191_4_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1191_4 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1192`: `(Rsh32x16 [false] x con:(Const16 [c])) && 0 < c && c < 32 => (Rsh32x16 [true] x con)` -/
theorem r_generic_1192_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1192 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1192`: `(Rsh32x32 [false] x con:(Const32 [c])) && 0 < c && c < 32 => (Rsh32x32 [true] x con)` -/
theorem r_generic_1192_2_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1192_2 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1192`: `(Rsh32x64 [false] x con:(Const64 [c])) && 0 < c && c < 32 => (Rsh32x64 [true] x con)` -/
theorem r_generic_1192_3_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1192_3 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1192`: `(Rsh32x8 [false] x con:(Const8 [c])) && 0 < c && c < 32 => (Rsh32x8 [true] x con)` -/
theorem r_generic_1192_4_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1192_4 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1193`: `(Rsh32Ux16 [false] x con:(Const16 [c])) && 0 < c && c < 32 => (Rsh32Ux16 [true] x con)` -/
theorem r_generic_1193_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1193 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1193`: `(Rsh32Ux32 [false] x con:(Const32 [c])) && 0 < c && c < 32 => (Rsh32Ux32 [true] x con)` -/
theorem r_generic_1193_2_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1193_2 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1193`: `(Rsh32Ux64 [false] x con:(Const64 [c])) && 0 < c && c < 32 => (Rsh32Ux64 [true] x con)` -/
theorem r_generic_1193_3_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1193_3 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1193`: `(Rsh32Ux8 [false] x con:(Const8 [c])) && 0 < c && c < 32 => (Rsh32Ux8 [true] x con)` -/
theorem r_generic_1193_4_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1193_4 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1194`: `(Lsh16x16 [false] x con:(Const16 [c])) && 0 < c && c < 16 => (Lsh16x16 [true] x con)` -/
theorem r_generic_1194_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1194 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1194`: `(Lsh16x32 [false] x con:(Const32 [c])) && 0 < c && c < 16 => (Lsh16x32 [true] x con)` -/
theorem r_generic_1194_2_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1194_2 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1194`: `(Lsh16x64 [false] x con:(Const64 [c])) && 0 < c && c < 16 => (Lsh16x64 [true] x con)` -/
theorem r_generic_1194_3_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1194_3 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1194`: `(Lsh16x8 [false] x con:(Const8 [c])) && 0 < c && c < 16 => (Lsh16x8 [true] x con)` -/
theorem r_generic_1194_4_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1194_4 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1195`: `(Rsh16x16 [false] x con:(Const16 [c])) && 0 < c && c < 16 => (Rsh16x16 [true] x con)` -/
theorem r_generic_1195_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1195 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1195`: `(Rsh16x32 [false] x con:(Const32 [c])) && 0 < c && c < 16 => (Rsh16x32 [true] x con)` -/
theorem r_generic_1195_2_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1195_2 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1195`: `(Rsh16x64 [false] x con:(Const64 [c])) && 0 < c && c < 16 => (Rsh16x64 [true] x con)` -/
theorem r_generic_1195_3_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1195_3 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1195`: `(Rsh16x8 [false] x con:(Const8 [c])) && 0 < c && c < 16 => (Rsh16x8 [true] x con)` -/
theorem r_generic_1195_4_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1195_4 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1196`: `(Rsh16Ux16 [false] x con:(Const16 [c])) && 0 < c && c < 16 => (Rsh16Ux16 [true] x con)` -/
theorem r_generic_1196_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1196 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1196`: `(Rsh16Ux32 [false] x con:(Const32 [c])) && 0 < c && c < 16 => (Rsh16Ux32 [true] x con)` -/
theorem r_generic_1196_2_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1196_2 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1196`: `(Rsh16Ux64 [false] x con:(Const64 [c])) && 0 < c && c < 16 => (Rsh16Ux64 [true] x con)` -/
theorem r_generic_1196_3_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1196_3 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1196`: `(Rsh16Ux8 [false] x con:(Const8 [c])) && 0 < c && c < 16 => (Rsh16Ux8 [true] x con)` -/
theorem r_generic_1196_4_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1196_4 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1197`: `(Lsh8x16 [false] x con:(Const16 [c])) && 0 < c && c < 8 => (Lsh8x16 [true] x con)` -/
theorem r_generic_1197_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1197 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1197`: `(Lsh8x32 [false] x con:(Const32 [c])) && 0 < c && c < 8 => (Lsh8x32 [true] x con)` -/
theorem r_generic_1197_2_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1197_2 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1197`: `(Lsh8x64 [false] x con:(Const64 [c])) && 0 < c && c < 8 => (Lsh8x64 [true] x con)` -/
theorem r_generic_1197_3_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1197_3 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1197`: `(Lsh8x8 [false] x con:(Const8 [c])) && 0 < c && c < 8 => (Lsh8x8 [true] x con)` -/
theorem r_generic_1197_4_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1197_4 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1198`: `(Rsh8x16 [false] x con:(Const16 [c])) && 0 < c && c < 8 => (Rsh8x16 [true] x con)` -/
theorem r_generic_1198_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1198 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1198`: `(Rsh8x32 [false] x con:(Const32 [c])) && 0 < c && c < 8 => (Rsh8x32 [true] x con)` -/
theorem r_generic_1198_2_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1198_2 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1198`: `(Rsh8x64 [false] x con:(Const64 [c])) && 0 < c && c < 8 => (Rsh8x64 [true] x con)` -/
theorem r_generic_1198_3_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1198_3 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-- `generic.rules:1198`: `(Rsh8x8 [false] x con:(Const8 [c])) && 0 < c && c < 8 => (Rsh8x8 [true] x con)` -/
theorem r_generic_1198_4_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1198_4 :=
  Rule.soundW_of_pure rfl (by rule_auto_w)

/-! ## Non-vacuity: a match narrower than its op -/

/-- The hypotheses of `Rule.SoundWP r` hold at the instance `e`, whose raw value does not have
the matched type's shape (`Rule.Sound` says nothing about it) and reads at that type as a
non-`poison` value. -/
def Rule.InstW (r : GoFV.Rules.Rule) (e : PEnv) (or : Oracle) : Prop :=
  Oracle.BoolTyped or ∧
  Pat.wf e [] r.pat ∧
  Pat.cons (evalE (r.vars.map (·.ty)) (sigma e r.pat) or e (Pat.den e [] r.pat)) (sigma e r.pat)
    e [] r.pat ∧
  condHolds (evalE (r.vars.map (·.ty)) (sigma e r.pat) or e (Pat.den e [] r.pat)) r.cond ∧
  Pat.typed e [] r.pat ∧
  Pat.argsOK e.ty [] r.pat = true ∧
  Pat.nonNegOK e r.pat r.cond = true ∧
  (Pat.raw e r.pat).hasTy (e.ty []) = false ∧
  (Pat.raw e r.pat).retype (e.ty []) ≠ .poison

/-- `generic.rules:1189` on an `Rsh64x16` typed `int32` (as divmod builds it): `x = -64`,
`c = 3`; the raw value is the 64-bit `-8`, read as the 32-bit `-8`. -/
theorem inst_r_generic_1189 : Rule.InstW GoFV.Rules.Generated.Generic.r_generic_1189
    (PEnv.ofLists [([0], .i64 (-64))] [([0], .int .w64), ([1], .int .w16)] (.int .w32) [([1], 3)])
    (Oracle.const true) := by
  simp [Rule.InstW, GoFV.Rules.Generated.Generic.r_generic_1189]
  rule_eval
  simp [Val.retype, Width.bits]

end GoFV.Proof.Rules
