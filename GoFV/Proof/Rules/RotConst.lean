import GoFV.Proof.Rules.ConstString
import GoFV.Rules.Generated.Generic.Values00
import GoFV.Rules.Generated.Generic.Values08
import GoFV.Rules.Generated.Generic.Values09
import GoFV.Rules.Generated.Generic.Values13
import GoFV.Rules.Generated.Generic.Values14

/-!
# Constant rotate detection (`generic.rules:2166–2169`, #69, #90)

`((Add|Or|Xor)<w> (Lsh<w>x64 x z:(Const64 [c])) (Rsh<w>Ux64 x (Const64 [d]))) && c < w &&
d == w-c && canRotate(config, w) => (RotateLeft<w> x z)` compares `c` signed: at `c = -1`,
`d = w+1` both shifts are 0 while `RotateLeft` rotates by `2^64-1`, i.e. by `w-1` (#90, a latent
Go bug: no trigger is known, the out-of-range shift folds win). `nonNegAuxs` names the auxint `c`
and `FrameOK` makes it nonnegative (the rewrite validator checks the instance's auxint,
`RewriteCheck.condFrameOK`); `canRotate` is an oracle conjunct, as for the proven `:2185`. Then
`0 ≤ c < w`, the amounts are `c` and `w - c` (`rot_amts`), the two shifted values have disjoint
bits and the sum, `or` and `xor` are the rotation (`rot_add`, `rot_or`, `rot_xor`). The 12 lemmas
hold under `Rule.SoundT` (`Rule.soundT_of_soundNN`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Rules.Generated.Generic

section

variable [GoFV.SSA.Sem.Addrs]

/-- The shift amounts of the constant rotate rules for `0 ≤ c < W ≤ 64`: `c` and `W - c`. -/
theorem rot_amts {c W : Int} (h0 : 0 ≤ c) (hc : c < W) (hW : W ≤ 64) :
    (BitVec.ofInt 64 c).toNat = c.toNat ∧
      (BitVec.ofInt 64 (wrapInt 64 true (W - c))).toNat = (W - c).toNat := by
  have hwr : wrapInt 64 true (W - c) = W - c := by rw [wrapInt64_omega]; omega
  rw [hwr, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  constructor
  · rw [Int.emod_eq_of_lt h0 (by simp; omega)]
  · rw [Int.emod_eq_of_lt (by omega) (by simp; omega)]

set_option hygiene false in
/-- Close a constant rotate goal `x <<< c ∘ x >>> (w - c) = x.rotateLeft c` (`∘` one of `+`,
`|||`, `^^^`; the amounts read from 64-bit constants) from `hc0 : 0 ≤ c` and the condition's
`c < w`. -/
local macro "rot_const" : tactic => `(tactic| (
  first
  | (obtain ⟨h1, h2⟩ := rot_amts (W := 64) hc0 (by omega) (by decide); rw [h1, h2])
  | (obtain ⟨h1, h2⟩ := rot_amts (W := 32) hc0 (by omega) (by decide); rw [h1, h2])
  | (obtain ⟨h1, h2⟩ := rot_amts (W := 16) hc0 (by omega) (by decide); rw [h1, h2])
  | (obtain ⟨h1, h2⟩ := rot_amts (W := 8) hc0 (by omega) (by decide); rw [h1, h2])
  first
  | exact rot_add _ _ _ (by omega) (by omega)
  | exact rot_or _ _ _ (by omega) (by omega)
  | exact rot_xor _ _ _ (by omega) (by omega)))

set_option hygiene false in
/-- `Rule.SoundNN` of a constant rotate rule: unfold, read `0 ≤ c` (`nonNegAuxs`), `rule_auto`'s
normalisation and case splits, `rot_const`. -/
local macro "rot_nn" : tactic => `(tactic| (
  rule_unfold
  intro hnl hna
  have hc0 := hna [1, 0] (by simp [nonNegAuxs])
  clear hnl hna
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals rot_const))

/-- `generic.rules:2166`: `(Add64 (Lsh64x64 x z:(Const64 <t> [c])) (Rsh64Ux64 x (Const64 [d]))) && c < 64 && d == 64-c && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2166_sound : Rule.SoundT r_generic_2166 :=
  Rule.soundT_of_soundNN (by rot_nn) rfl

/-- `generic.rules:2167`: `(Add32 (Lsh32x64 x z:(Const64 <t> [c])) (Rsh32Ux64 x (Const64 [d]))) && c < 32 && d == 32-c && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2167_sound : Rule.SoundT r_generic_2167 :=
  Rule.soundT_of_soundNN (by rot_nn) rfl

/-- `generic.rules:2168`: `(Add16 (Lsh16x64 x z:(Const64 <t> [c])) (Rsh16Ux64 x (Const64 [d]))) && c < 16 && d == 16-c && canRotate(config, 16) => (RotateLeft16 x z)` -/
theorem r_generic_2168_sound : Rule.SoundT r_generic_2168 :=
  Rule.soundT_of_soundNN (by rot_nn) rfl

/-- `generic.rules:2169`: `(Add8 (Lsh8x64 x z:(Const64 <t> [c])) (Rsh8Ux64 x (Const64 [d]))) && c < 8 && d == 8-c && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2169_sound : Rule.SoundT r_generic_2169 :=
  Rule.soundT_of_soundNN (by rot_nn) rfl

/-- `generic.rules:2166`: `(Or64 (Lsh64x64 x z:(Const64 <t> [c])) (Rsh64Ux64 x (Const64 [d]))) && c < 64 && d == 64-c && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2166_2_sound : Rule.SoundT r_generic_2166_2 :=
  Rule.soundT_of_soundNN (by rot_nn) rfl

/-- `generic.rules:2167`: `(Or32 (Lsh32x64 x z:(Const64 <t> [c])) (Rsh32Ux64 x (Const64 [d]))) && c < 32 && d == 32-c && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2167_2_sound : Rule.SoundT r_generic_2167_2 :=
  Rule.soundT_of_soundNN (by rot_nn) rfl

/-- `generic.rules:2168`: `(Or16 (Lsh16x64 x z:(Const64 <t> [c])) (Rsh16Ux64 x (Const64 [d]))) && c < 16 && d == 16-c && canRotate(config, 16) => (RotateLeft16 x z)` -/
theorem r_generic_2168_2_sound : Rule.SoundT r_generic_2168_2 :=
  Rule.soundT_of_soundNN (by rot_nn) rfl

/-- `generic.rules:2169`: `(Or8 (Lsh8x64 x z:(Const64 <t> [c])) (Rsh8Ux64 x (Const64 [d]))) && c < 8 && d == 8-c && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2169_2_sound : Rule.SoundT r_generic_2169_2 :=
  Rule.soundT_of_soundNN (by rot_nn) rfl

/-- `generic.rules:2166`: `(Xor64 (Lsh64x64 x z:(Const64 <t> [c])) (Rsh64Ux64 x (Const64 [d]))) && c < 64 && d == 64-c && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2166_3_sound : Rule.SoundT r_generic_2166_3 :=
  Rule.soundT_of_soundNN (by rot_nn) rfl

/-- `generic.rules:2167`: `(Xor32 (Lsh32x64 x z:(Const64 <t> [c])) (Rsh32Ux64 x (Const64 [d]))) && c < 32 && d == 32-c && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2167_3_sound : Rule.SoundT r_generic_2167_3 :=
  Rule.soundT_of_soundNN (by rot_nn) rfl

/-- `generic.rules:2168`: `(Xor16 (Lsh16x64 x z:(Const64 <t> [c])) (Rsh16Ux64 x (Const64 [d]))) && c < 16 && d == 16-c && canRotate(config, 16) => (RotateLeft16 x z)` -/
theorem r_generic_2168_3_sound : Rule.SoundT r_generic_2168_3 :=
  Rule.soundT_of_soundNN (by rot_nn) rfl

/-- `generic.rules:2169`: `(Xor8 (Lsh8x64 x z:(Const64 <t> [c])) (Rsh8Ux64 x (Const64 [d]))) && c < 8 && d == 8-c && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2169_3_sound : Rule.SoundT r_generic_2169_3 :=
  Rule.soundT_of_soundNN (by rot_nn) rfl

end

/-! ## Non-vacuity -/

open scoped GoFV.SSA.Sem.Fixed

set_option hygiene false in
/-- `Rule.InstT` of a constant rotate rule at `x = 5`, `c = 3`, `d = w - 3`: the built
`RotateLeft` has no frame helpers, `c` is nonnegative (`nonNegAuxs`), the oracle answers
`canRotate` `true`. -/
local macro "rot_inst" r:ident : tactic => `(tactic| (
  refine ⟨Oracle.const_boolTyped true, ?_, ?_⟩
  · refine ⟨fun n hn => ?_, by simp [$r:ident, emptyStrVars], by simp [$r:ident, samePtrVars],
      by simp [$r:ident, numElem1Vars], by simp [$r:ident, size0Vars],
      by simp [$r:ident, sameLeaves], by simp [$r:ident, nonNegLeaves], fun p hp => ?_⟩
    · simp only [$r:ident, Result.nodes, List.mem_cons, List.not_mem_nil, or_false] at hn
      subst hn
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a b h <;> simp at h
    · simp [$r:ident, nonNegAuxs] at hp
      subst hp
      decide
  · simp [$r:ident, Pat.rawT, Pat.densT, Pat.denT, sigmaT, Pat.bindsT, Pat.bindssT, opVal]
    rule_eval
    all_goals (simp [sigmaT, Pat.bindsT, Pat.bindssT, List.lookup, auxIntDV]; try rule_eval)))

/-- `generic.rules:2166` (`Add64`) at `5 <<< 3 + 5 >>> 61`. -/
theorem inst_r_generic_2166 : Rule.InstT r_generic_2166 {}
    (PEnv.ofLists [([0, 0], .i64 5), ([0, 1], .i64 5)] [] (.int .w64) [([1, 0], 3), ([1, 1], 61)])
    (Oracle.const true) := by
  rot_inst r_generic_2166

/-- `generic.rules:2167` (`Add32`) at `5 <<< 3 + 5 >>> 29`. -/
theorem inst_r_generic_2167 : Rule.InstT r_generic_2167 {}
    (PEnv.ofLists [([0, 0], .i32 5), ([0, 1], .i32 5)] [([1, 0], .int .w64), ([1, 1], .int .w64)]
      (.int .w32) [([1, 0], 3), ([1, 1], 29)])
    (Oracle.const true) := by
  rot_inst r_generic_2167

/-- `generic.rules:2168` (`Add16`) at `5 <<< 3 + 5 >>> 13`. -/
theorem inst_r_generic_2168 : Rule.InstT r_generic_2168 {}
    (PEnv.ofLists [([0, 0], .i16 5), ([0, 1], .i16 5)] [([1, 0], .int .w64), ([1, 1], .int .w64)]
      (.int .w16) [([1, 0], 3), ([1, 1], 13)])
    (Oracle.const true) := by
  rot_inst r_generic_2168

/-- `generic.rules:2169` (`Add8`) at `5 <<< 3 + 5 >>> 5`. -/
theorem inst_r_generic_2169 : Rule.InstT r_generic_2169 {}
    (PEnv.ofLists [([0, 0], .i8 5), ([0, 1], .i8 5)] [([1, 0], .int .w64), ([1, 1], .int .w64)]
      (.int .w8) [([1, 0], 3), ([1, 1], 5)])
    (Oracle.const true) := by
  rot_inst r_generic_2169

/-- `generic.rules:2166` (`Or64`) at `5 <<< 3 ||| 5 >>> 61`. -/
theorem inst_r_generic_2166_2 : Rule.InstT r_generic_2166_2 {}
    (PEnv.ofLists [([0, 0], .i64 5), ([0, 1], .i64 5)] [] (.int .w64) [([1, 0], 3), ([1, 1], 61)])
    (Oracle.const true) := by
  rot_inst r_generic_2166_2

/-- `generic.rules:2167` (`Or32`) at `5 <<< 3 ||| 5 >>> 29`. -/
theorem inst_r_generic_2167_2 : Rule.InstT r_generic_2167_2 {}
    (PEnv.ofLists [([0, 0], .i32 5), ([0, 1], .i32 5)] [([1, 0], .int .w64), ([1, 1], .int .w64)]
      (.int .w32) [([1, 0], 3), ([1, 1], 29)])
    (Oracle.const true) := by
  rot_inst r_generic_2167_2

/-- `generic.rules:2168` (`Or16`) at `5 <<< 3 ||| 5 >>> 13`. -/
theorem inst_r_generic_2168_2 : Rule.InstT r_generic_2168_2 {}
    (PEnv.ofLists [([0, 0], .i16 5), ([0, 1], .i16 5)] [([1, 0], .int .w64), ([1, 1], .int .w64)]
      (.int .w16) [([1, 0], 3), ([1, 1], 13)])
    (Oracle.const true) := by
  rot_inst r_generic_2168_2

/-- `generic.rules:2169` (`Or8`) at `5 <<< 3 ||| 5 >>> 5`. -/
theorem inst_r_generic_2169_2 : Rule.InstT r_generic_2169_2 {}
    (PEnv.ofLists [([0, 0], .i8 5), ([0, 1], .i8 5)] [([1, 0], .int .w64), ([1, 1], .int .w64)]
      (.int .w8) [([1, 0], 3), ([1, 1], 5)])
    (Oracle.const true) := by
  rot_inst r_generic_2169_2

/-- `generic.rules:2166` (`Xor64`) at `5 <<< 3 ^^^ 5 >>> 61`. -/
theorem inst_r_generic_2166_3 : Rule.InstT r_generic_2166_3 {}
    (PEnv.ofLists [([0, 0], .i64 5), ([0, 1], .i64 5)] [] (.int .w64) [([1, 0], 3), ([1, 1], 61)])
    (Oracle.const true) := by
  rot_inst r_generic_2166_3

/-- `generic.rules:2167` (`Xor32`) at `5 <<< 3 ^^^ 5 >>> 29`. -/
theorem inst_r_generic_2167_3 : Rule.InstT r_generic_2167_3 {}
    (PEnv.ofLists [([0, 0], .i32 5), ([0, 1], .i32 5)] [([1, 0], .int .w64), ([1, 1], .int .w64)]
      (.int .w32) [([1, 0], 3), ([1, 1], 29)])
    (Oracle.const true) := by
  rot_inst r_generic_2167_3

/-- `generic.rules:2168` (`Xor16`) at `5 <<< 3 ^^^ 5 >>> 13`. -/
theorem inst_r_generic_2168_3 : Rule.InstT r_generic_2168_3 {}
    (PEnv.ofLists [([0, 0], .i16 5), ([0, 1], .i16 5)] [([1, 0], .int .w64), ([1, 1], .int .w64)]
      (.int .w16) [([1, 0], 3), ([1, 1], 13)])
    (Oracle.const true) := by
  rot_inst r_generic_2168_3

/-- `generic.rules:2169` (`Xor8`) at `5 <<< 3 ^^^ 5 >>> 5`. -/
theorem inst_r_generic_2169_3 : Rule.InstT r_generic_2169_3 {}
    (PEnv.ofLists [([0, 0], .i8 5), ([0, 1], .i8 5)] [([1, 0], .int .w64), ([1, 1], .int .w64)]
      (.int .w8) [([1, 0], 3), ([1, 1], 5)])
    (Oracle.const true) := by
  rot_inst r_generic_2169_3

end GoFV.Proof.Rules
