import GoFV.Proof.Rules.ConstString
import GoFV.Rules.Generated.Generic.Values05

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: a masked right shift shifted back left (`generic.rules:574`)

`(Lsh64x64 (And64 (Rsh64x64 <t> x (Const64 <t2> [c])) (Const64 [d])) (Const64 [e])) && c >= e =>
(And64 (Rsh64x64 <t> x (Const64 <t2> [c-e])) (Const64 <t> [d<<e]))` and its `Rsh64Ux64` twin,
under `Rule.SoundT` (`DenT.lean`): the built auxint `d<<e` is a shift, so `FrameOK` (which the
rewrite validator checks, `frameNodeOK`) says that `e ≥ 0` (Go panics on a negative shift
amount: the rewriter built no node). Then `0 ≤ e ≤ c`, `c - e` does not wrap, and bit by bit
`((x >> c) & d) << e = (x >> (c - e)) & (d << e)` (`sshiftRight_and_shiftLeft`,
`ushiftRight_and_shiftLeft`; issue #69). Without `e ≥ 0` the rule is false in the model: the
source shifts by `e` as an unsigned amount (≥ 2^63, so 0) and `d<<e` is the oracle's.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

theorem sshiftRight_and_shiftLeft {w : Nat} (x d : BitVec w) {c s : Nat} (h : s ≤ c) :
    (x.sshiftRight c &&& d) <<< s = x.sshiftRight (c - s) &&& d <<< s := by
  ext i hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_and, BitVec.getElem_sshiftRight]
  by_cases his : i < s
  · simp [his]
  · have : c + (i - s) = c - s + i := by omega
    simp only [his, this, decide_false, Bool.not_false, Bool.true_and]

theorem ushiftRight_and_shiftLeft {w : Nat} (x d : BitVec w) {c s : Nat} (h : s ≤ c) :
    (x >>> c &&& d) <<< s = x >>> (c - s) &&& d <<< s := by
  ext i hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_and, BitVec.getElem_ushiftRight]
  by_cases his : i < s
  · simp [his]
  · have : c + (i - s) = c - s + i := by omega
    simp only [his, this, decide_false, Bool.not_false, Bool.true_and]

set_option hygiene false in
/-- The proof of both `:574` rules: `e ≥ 0` from `FrameOK` (the built `d<<e`), then
`rule_auto`'s unfolding and case splits; the cases with `e < 0` close by `omega`, the others by
the bit identity (unhygienic: `rule_unfold`'s tactics find the hypotheses by name). -/
local macro "shift_mask" r:ident : tactic => `(tactic| (
  refine ⟨rfl, fun tabs e or hbt => ?_⟩
  simp only [sigmaT_pure tabs e (pat := (Rule.pat $r)) rfl,
    Pat.denT_pure tabs e [] (Rule.pat $r) rfl,
    Pat.rawT_pure tabs e (pat := (Rule.pat $r)) rfl,
    resDenT_pure tabs _ or _ _ (res := (Rule.result $r)) rfl]
  intro hfr
  obtain ⟨i, hi, hi0⟩ := (hfr.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))).2.2.2 _ (.var 5) rfl rfl
  clear hfr
  dsimp only [$r:ident, rule_unfold_ds] at hi ⊢
  simp only [rule_helper, rule_unfold_s] at hi ⊢
  have he : 0 ≤ (e.auxInt [1]).toInt := by cases hi; exact hi0
  clear hi hi0
  intro hwf hc hcond hty hlt hat hnn
  (try dsimp only [GoFV.Proof.Rules.condHolds, rule_unfold_ds] at hcond)
  (try simp only [rule_helper, rule_unfold_s] at hcond)
  rule_oracle_bool
  rule_cond_bool
  clear hat hnn
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals first
    | omega
    | (have hc1 := Int64.toInt_lt (e.auxInt [1, 0, 0])
       rw [ofInt_wrapInt_true (Nat.le_refl 64), ofInt_wrapInt_true (Nat.le_refl 64),
         ofInt_goShl (Nat.le_refl 64)]
       have h1 : (BitVec.ofInt 64 (e.auxInt [1, 0, 0]).toInt).toNat =
           (e.auxInt [1, 0, 0]).toInt.toNat := by
         simp only [BitVec.toNat_ofInt]; omega
       have h2 : (BitVec.ofInt 64 (e.auxInt [1]).toInt).toNat = (e.auxInt [1]).toInt.toNat := by
         simp only [BitVec.toNat_ofInt]; omega
       have h3 : (BitVec.ofInt 64 ((e.auxInt [1, 0, 0]).toInt - (e.auxInt [1]).toInt)).toNat =
           (e.auxInt [1, 0, 0]).toInt.toNat - (e.auxInt [1]).toInt.toNat := by
         simp only [BitVec.toNat_ofInt]; omega
       rw [h1, h2, h3]
       first
         | with_reducible exact sshiftRight_and_shiftLeft _ _ (by omega)
         | with_reducible exact ushiftRight_and_shiftLeft _ _ (by omega))))

/-- `generic.rules:574`: `(Lsh64x64 (And64 (Rsh64x64 <t> x (Const64 <t2> [c])) (Const64 [d])) (Const64 [e])) && c >= e => (And64 (Rsh64x64 <t> x (Const64 <t2> [c-e])) (Const64 <t> [d<<e]))` -/
theorem r_generic_574_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_574 := by
  shift_mask GoFV.Rules.Generated.Generic.r_generic_574

/-- `generic.rules:574`: `(Lsh64x64 (And64 (Rsh64Ux64 <t> x (Const64 <t2> [c])) (Const64 [d])) (Const64 [e])) && c >= e => (And64 (Rsh64Ux64 <t> x (Const64 <t2> [c-e])) (Const64 <t> [d<<e]))` -/
theorem r_generic_574_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_574_2 := by
  shift_mask GoFV.Rules.Generated.Generic.r_generic_574_2

/-! ## Non-vacuity (`rule-sat` draws no tables) -/

/-- The instance of both `:574` rules: `x = 0x1234`, `c = 4`, `d = 0xff`, `e = 2`, all `int64`. -/
def shiftMaskEnv : PEnv where
  leaf p := if p = [0, 0, 0] then .int .w64 0x1234 else .poison
  ty _ := .int .w64
  auxInt p := if p = [1, 0, 0] then 4 else if p = [1, 0] then 0xff else if p = [1] then 2 else 0
  aux _ := none

set_option hygiene false in
/-- The non-vacuity proof of both `:574` rules at `shiftMaskEnv`. -/
local macro "shift_mask_inst" r:ident : tactic => `(tactic| (
  refine ⟨Oracle.const_boolTyped true, ?_⟩
  dsimp only
  refine ⟨?_, ?_⟩
  · unfold FrameOK
    refine ⟨fun n hn => ?_, by simp [$r:ident, emptyStrVars],
      by simp [$r:ident, samePtrVars], by simp [$r:ident, numElem1Vars],
      by simp [$r:ident, size0Vars], by simp [$r:ident, sameLeaves],
      by simp [$r:ident, nonNegLeaves]⟩
    simp only [$r:ident, Result.nodes, List.mem_cons,
      List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a b h hb <;>
      simp only [reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
      simp [lenVar?, shiftAmt?] at hb ⊢
    subst hb
    exact ⟨2, by simp [evalE, sigmaT, Pat.bindsT, Pat.bindssT, shiftMaskEnv, List.lookup, auxIntDV,
      $r:ident], by decide⟩
  · simp [$r:ident, Pat.rawT, Pat.densT, Pat.denT, sigmaT,
      Pat.bindsT, Pat.bindssT, shiftMaskEnv, opVal]
    rule_eval
    simp [sigmaT, Pat.bindsT, Pat.bindssT, shiftMaskEnv, List.lookup, auxIntDV]))

/-- `generic.rules:574` at `((0x1234 >> 4) & 0xff) << 2`. -/
theorem inst_r_generic_574 : Rule.InstT GoFV.Rules.Generated.Generic.r_generic_574 {}
    shiftMaskEnv (Oracle.const true) := by
  shift_mask_inst GoFV.Rules.Generated.Generic.r_generic_574

/-- `generic.rules:574` (`Rsh64Ux64`) at `((0x1234 >>> 4) & 0xff) << 2`. -/
theorem inst_r_generic_574_2 : Rule.InstT GoFV.Rules.Generated.Generic.r_generic_574_2 {}
    shiftMaskEnv (Oracle.const true) := by
  shift_mask_inst GoFV.Rules.Generated.Generic.r_generic_574_2

end GoFV.Proof.Rules
