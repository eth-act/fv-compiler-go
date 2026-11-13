import GoFV.Proof.Rules.ConstString
import GoFV.Rules.Generated.Generic.Values02

/-!
# Rule lemmas: `CondSelect` into arithmetic (`generic.rules:2321–2394`)

`(CondSelect op:(Add64 <t> x c:(Const64)) x bool) && rewriteCondSelectIntoMath(…) => (Add64 x
(Mul64 <t> c (ZeroExt8to64 <t> (CvtBoolToUint8 bool))))`, its `x`-first form on `Not bool`, the
`Sub` forms on `-c`, the `Or`/`Xor` forms and the shifts by 1, at every width (56 rules), under
`Rule.SoundT` (`DenT.lean`). Where the select takes the plain arm the matched value is the leaf
`x` itself and the result recomputes `x op 0` (`x op c·0`, `x << 0`): false under the bare
semantics (`docs/proofs/rules.md`, "Findings") when `x` is not an integer of the op's width, which
a 64-bit integer shape allows (a pointer without an integer form, `Val.hasTy`), or when the arm,
its constant or the select are typed otherwise. Go builds them all at the op's width, and the
rewrite validator checks it on the instance, and at 64 bits that `x` is an integer or `poison`
(`RewriteCheck.condMathOKD`: `intDW`, sound by `intDW_den`); `FrameOK` carries the facts
(`condMathFacts`, `CondMathOK`) and `Rule.soundT_of_condMath` reduces each lemma to
`Rule.SoundCM`, which `cm_auto` proves as `rule_auto` proves `Rule.Sound`: the facts rewrite the
types and the leaf, then the case splits (the condition's boolean among them) and `rule_close`.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

section

variable [GoFV.SSA.Sem.Addrs]

/-- `Rule.SoundCM` of a `CondSelect` into arithmetic rule under its `condMathFacts`: the shapes
rewrite the types and the leaf `x` is split into `poison` or an integer, then `rule_auto`'s
splits, the select's boolean as an `if`, and `rule_close` (a `poison` source refined by
anything, a recomputed `x` by itself). -/
local macro "cm_auto" : tactic => `(tactic| (
  rule_unfold
  intro hcm
  obtain ⟨h0, h1, h2, h3, hx⟩ := hcm
  rcases hx with hx | ⟨xv, hx⟩ <;> simp only [h0, h1, h2, h3, hx] at *
  all_goals (try rule_ands)
  all_goals (try rule_clear_oracle)
  all_goals (try rule_norm)
  all_goals (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try simp only [Bool.cond_eq_ite] at *)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals (try simp (disch := decide) only [Bool.cond_self, BitVec.ofInt_neg,
    ofInt_wrapInt_true, BitVec.toNat_zero, BitVec.shiftLeft_zero, Nat.le_zero,
    OfNat.ofNat_ne_zero, reduceIte] at *)
  all_goals first
    | exact Refines.refl _
    | exact Refines.poison _
    | rule_close
    | (simp [Val.retype] <;> exact Refines.refl _)))

/-- `generic.rules:2322`: `(CondSelect op:(Add8 <t> x c:(Const8)) x bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Add8 x (Mul8 <t> c (CvtBoolToUint8 <t> bool)))` -/
theorem r_generic_2322_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2322 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w8) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2325`: `(CondSelect op:(Add64 <t> x c:(Const64)) x bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Add64 x (Mul64 <t> c (ZeroExt8to64 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))))` -/
theorem r_generic_2325_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2325 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2325`: `(CondSelect op:(Add32 <t> x c:(Const32)) x bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Add32 x (Mul32 <t> c (ZeroExt8to32 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))))` -/
theorem r_generic_2325_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2325_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w32) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2325`: `(CondSelect op:(Add16 <t> x c:(Const16)) x bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Add16 x (Mul16 <t> c (ZeroExt8to16 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))))` -/
theorem r_generic_2325_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2325_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w16) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2329`: `(CondSelect x op:(Add8 <t> x c:(Const8)) bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Add8 x (Mul8 <t> c (CvtBoolToUint8 <t> (Not <bool.Type> bool))))` -/
theorem r_generic_2329_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2329 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w8) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2332`: `(CondSelect x op:(Add64 <t> x c:(Const64)) bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Add64 x (Mul64 <t> c (ZeroExt8to64 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))))` -/
theorem r_generic_2332_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2332 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2332`: `(CondSelect x op:(Add32 <t> x c:(Const32)) bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Add32 x (Mul32 <t> c (ZeroExt8to32 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))))` -/
theorem r_generic_2332_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2332_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w32) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2332`: `(CondSelect x op:(Add16 <t> x c:(Const16)) bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Add16 x (Mul16 <t> c (ZeroExt8to16 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))))` -/
theorem r_generic_2332_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2332_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w16) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2338`: `(CondSelect op:(Add8 <t> x c:(Const8 [consT])) x bool) && !rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) && rewriteCondSelectIntoMath(config, addToSub(op.Op), -c.AuxInt) => (Sub8 x (Mul8 <t> (Const8 <t> [-consT]) (CvtBoolToUint8 <t> bool)))` -/
theorem r_generic_2338_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2338 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w8) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2342`: `(CondSelect op:(Add64 <t> x c:(Const64 [consT])) x bool) && !rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) && rewriteCondSelectIntoMath(config, addToSub(op.Op), -c.AuxInt) => (Sub64 x (Mul64 <t> (Const64 <t> [-consT]) (ZeroExt8to64 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))))` -/
theorem r_generic_2342_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2342 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2342`: `(CondSelect op:(Add32 <t> x c:(Const32 [consT])) x bool) && !rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) && rewriteCondSelectIntoMath(config, addToSub(op.Op), -c.AuxInt) => (Sub32 x (Mul32 <t> (Const32 <t> [-consT]) (ZeroExt8to32 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))))` -/
theorem r_generic_2342_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2342_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w32) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2342`: `(CondSelect op:(Add16 <t> x c:(Const16 [consT])) x bool) && !rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) && rewriteCondSelectIntoMath(config, addToSub(op.Op), -c.AuxInt) => (Sub16 x (Mul16 <t> (Const16 <t> [-consT]) (ZeroExt8to16 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))))` -/
theorem r_generic_2342_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2342_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w16) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2347`: `(CondSelect x op:(Add8 <t> x c:(Const8 [consT])) bool) && !rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) && rewriteCondSelectIntoMath(config, addToSub(op.Op), -c.AuxInt) => (Sub8 x (Mul8 <t> (Const8 <t> [-consT]) (CvtBoolToUint8 <t> (Not <bool.Type> bool))))` -/
theorem r_generic_2347_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2347 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w8) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2351`: `(CondSelect x op:(Add64 <t> x c:(Const64 [consT])) bool) && !rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) && rewriteCondSelectIntoMath(config, addToSub(op.Op), -c.AuxInt) => (Sub64 x (Mul64 <t> (Const64 <t> [-consT]) (ZeroExt8to64 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))))` -/
theorem r_generic_2351_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2351 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2351`: `(CondSelect x op:(Add32 <t> x c:(Const32 [consT])) bool) && !rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) && rewriteCondSelectIntoMath(config, addToSub(op.Op), -c.AuxInt) => (Sub32 x (Mul32 <t> (Const32 <t> [-consT]) (ZeroExt8to32 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))))` -/
theorem r_generic_2351_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2351_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w32) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2351`: `(CondSelect x op:(Add16 <t> x c:(Const16 [consT])) bool) && !rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) && rewriteCondSelectIntoMath(config, addToSub(op.Op), -c.AuxInt) => (Sub16 x (Mul16 <t> (Const16 <t> [-consT]) (ZeroExt8to16 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))))` -/
theorem r_generic_2351_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2351_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w16) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2355`: `(CondSelect (Lsh64x64 x (Const64 [1])) x bool) => (Lsh64x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))` -/
theorem r_generic_2355_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2355 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2355`: `(CondSelect (Lsh32x64 x (Const64 [1])) x bool) => (Lsh32x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))` -/
theorem r_generic_2355_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2355_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2355`: `(CondSelect (Lsh16x64 x (Const64 [1])) x bool) => (Lsh16x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))` -/
theorem r_generic_2355_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2355_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2355`: `(CondSelect (Lsh8x64 x (Const64 [1])) x bool) => (Lsh8x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))` -/
theorem r_generic_2355_4_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2355_4 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2357`: `(CondSelect x (Lsh64x64 x (Const64 [1])) bool) => (Lsh64x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))` -/
theorem r_generic_2357_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2357 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2357`: `(CondSelect x (Lsh32x64 x (Const64 [1])) bool) => (Lsh32x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))` -/
theorem r_generic_2357_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2357_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2357`: `(CondSelect x (Lsh16x64 x (Const64 [1])) bool) => (Lsh16x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))` -/
theorem r_generic_2357_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2357_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2357`: `(CondSelect x (Lsh8x64 x (Const64 [1])) bool) => (Lsh8x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))` -/
theorem r_generic_2357_4_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2357_4 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2360`: `(CondSelect (Rsh64x64 x (Const64 [1])) x bool) => (Rsh64x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))` -/
theorem r_generic_2360_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2360 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2360`: `(CondSelect (Rsh32x64 x (Const64 [1])) x bool) => (Rsh32x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))` -/
theorem r_generic_2360_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2360_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2360`: `(CondSelect (Rsh16x64 x (Const64 [1])) x bool) => (Rsh16x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))` -/
theorem r_generic_2360_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2360_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2360`: `(CondSelect (Rsh8x64 x (Const64 [1])) x bool) => (Rsh8x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))` -/
theorem r_generic_2360_4_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2360_4 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2361`: `(CondSelect (Rsh64Ux64 x (Const64 [1])) x bool) => (Rsh64Ux8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))` -/
theorem r_generic_2361_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2361 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2361`: `(CondSelect (Rsh32Ux64 x (Const64 [1])) x bool) => (Rsh32Ux8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))` -/
theorem r_generic_2361_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2361_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2361`: `(CondSelect (Rsh16Ux64 x (Const64 [1])) x bool) => (Rsh16Ux8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))` -/
theorem r_generic_2361_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2361_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2361`: `(CondSelect (Rsh8Ux64 x (Const64 [1])) x bool) => (Rsh8Ux8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))` -/
theorem r_generic_2361_4_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2361_4 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2363`: `(CondSelect x (Rsh64x64 x (Const64 [1])) bool) => (Rsh64x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))` -/
theorem r_generic_2363_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2363 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2363`: `(CondSelect x (Rsh32x64 x (Const64 [1])) bool) => (Rsh32x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))` -/
theorem r_generic_2363_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2363_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2363`: `(CondSelect x (Rsh16x64 x (Const64 [1])) bool) => (Rsh16x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))` -/
theorem r_generic_2363_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2363_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2363`: `(CondSelect x (Rsh8x64 x (Const64 [1])) bool) => (Rsh8x8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))` -/
theorem r_generic_2363_4_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2363_4 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2364`: `(CondSelect x (Rsh64Ux64 x (Const64 [1])) bool) => (Rsh64Ux8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))` -/
theorem r_generic_2364_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2364 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2364`: `(CondSelect x (Rsh32Ux64 x (Const64 [1])) bool) => (Rsh32Ux8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))` -/
theorem r_generic_2364_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2364_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2364`: `(CondSelect x (Rsh16Ux64 x (Const64 [1])) bool) => (Rsh16Ux8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))` -/
theorem r_generic_2364_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2364_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2364`: `(CondSelect x (Rsh8Ux64 x (Const64 [1])) bool) => (Rsh8Ux8 [true] x (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))` -/
theorem r_generic_2364_4_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2364_4 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2368`: `(CondSelect op:(Or8 <t> x c:(Const8)) x bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Or8 x (Mul8 <t> c (CvtBoolToUint8 <t> bool)))` -/
theorem r_generic_2368_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2368 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w8) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2371`: `(CondSelect op:(Or64 <t> x c:(Const64)) x bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Or64 x (Mul64 <t> c (ZeroExt8to64 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))))` -/
theorem r_generic_2371_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2371 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2371`: `(CondSelect op:(Or32 <t> x c:(Const32)) x bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Or32 x (Mul32 <t> c (ZeroExt8to32 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))))` -/
theorem r_generic_2371_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2371_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w32) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2371`: `(CondSelect op:(Or16 <t> x c:(Const16)) x bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Or16 x (Mul16 <t> c (ZeroExt8to16 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))))` -/
theorem r_generic_2371_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2371_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w16) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2375`: `(CondSelect x op:(Or8 <t> x c:(Const8)) bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Or8 x (Mul8 <t> c (CvtBoolToUint8 <t> (Not <bool.Type> bool))))` -/
theorem r_generic_2375_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2375 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w8) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2378`: `(CondSelect x op:(Or64 <t> x c:(Const64)) bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Or64 x (Mul64 <t> c (ZeroExt8to64 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))))` -/
theorem r_generic_2378_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2378 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2378`: `(CondSelect x op:(Or32 <t> x c:(Const32)) bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Or32 x (Mul32 <t> c (ZeroExt8to32 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))))` -/
theorem r_generic_2378_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2378_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w32) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2378`: `(CondSelect x op:(Or16 <t> x c:(Const16)) bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Or16 x (Mul16 <t> c (ZeroExt8to16 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))))` -/
theorem r_generic_2378_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2378_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w16) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2383`: `(CondSelect op:(Xor8 <t> x c:(Const8)) x bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Xor8 x (Mul8 <t> c (CvtBoolToUint8 <t> bool)))` -/
theorem r_generic_2383_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2383 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w8) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2386`: `(CondSelect op:(Xor64 <t> x c:(Const64)) x bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Xor64 x (Mul64 <t> c (ZeroExt8to64 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))))` -/
theorem r_generic_2386_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2386 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2386`: `(CondSelect op:(Xor32 <t> x c:(Const32)) x bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Xor32 x (Mul32 <t> c (ZeroExt8to32 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))))` -/
theorem r_generic_2386_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2386_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w32) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2386`: `(CondSelect op:(Xor16 <t> x c:(Const16)) x bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Xor16 x (Mul16 <t> c (ZeroExt8to16 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> bool))))` -/
theorem r_generic_2386_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2386_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w16) (q := [0]) (px := [0, 0]) rfl rfl (by cm_auto)

/-- `generic.rules:2390`: `(CondSelect x op:(Xor8 <t> x c:(Const8)) bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Xor8 x (Mul8 <t> c (CvtBoolToUint8 <t> (Not <bool.Type> bool))))` -/
theorem r_generic_2390_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2390 :=
  Rule.soundT_of_condMath (w := .w8) (wc := .w8) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2393`: `(CondSelect x op:(Xor64 <t> x c:(Const64)) bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Xor64 x (Mul64 <t> c (ZeroExt8to64 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))))` -/
theorem r_generic_2393_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2393 :=
  Rule.soundT_of_condMath (w := .w64) (wc := .w64) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2393`: `(CondSelect x op:(Xor32 <t> x c:(Const32)) bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Xor32 x (Mul32 <t> c (ZeroExt8to32 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))))` -/
theorem r_generic_2393_2_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2393_2 :=
  Rule.soundT_of_condMath (w := .w32) (wc := .w32) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

/-- `generic.rules:2393`: `(CondSelect x op:(Xor16 <t> x c:(Const16)) bool) && rewriteCondSelectIntoMath(config, op.Op, c.AuxInt) => (Xor16 x (Mul16 <t> c (ZeroExt8to16 <t> (CvtBoolToUint8 <types.Types[types.TUINT8]> (Not <bool.Type> bool)))))` -/
theorem r_generic_2393_3_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_2393_3 :=
  Rule.soundT_of_condMath (w := .w16) (wc := .w16) (q := [1]) (px := [0]) rfl rfl (by cm_auto)

end

open scoped GoFV.SSA.Sem.Fixed

/-! ## Non-vacuity -/

/-- `generic.rules:2325` (64 bits) at `x = 5`, `c = 8` and `bool = false`: the select takes the
plain arm, the matched value is `x`, and every hypothesis of `Rule.SoundT`, the
`condMathFacts` among them (`FrameOK`), holds. -/
theorem inst_r_generic_2325 : Rule.InstT GoFV.Rules.Generated.Generic.r_generic_2325 {}
    { leaf := fun p => if p = [2] then .bool false else .int .w64 5
      ty := fun p => if p = [2] then .bool else .int .w64
      auxInt := fun p => if p = [1, 0] then 8 else 0, aux := fun _ => none }
    (Oracle.const true) := by
  refine ⟨Oracle.const_boolTyped true, ?_⟩
  simp [GoFV.Rules.Generated.Generic.r_generic_2325, FrameOK, CondMathOK, condMath?, condMathArm,
    condMathOp, condMathFacts, Result.nodes, samePtrVars, sameLeaves, numElem1Vars, size0Vars,
    shiftAmt?, Pat.leafPos, Pat.leafPoss, Pat.rawT, Pat.densT, Pat.denT, emptyStrVars, opVal]
  rule_eval
  refine ⟨by rintro _ _ _ _ rfl rfl rfl rfl; simp, ?_⟩
  simp [sigmaT, Pat.bindsT, Pat.bindssT, List.lookup, Pat.denT]

/-- `generic.rules:2322` (8 bits) at `x = 5`, `c = 4` and `bool = false`, as
`inst_r_generic_2325`. -/
theorem inst_r_generic_2322 : Rule.InstT GoFV.Rules.Generated.Generic.r_generic_2322 {}
    { leaf := fun p => if p = [2] then .bool false else .int .w8 5
      ty := fun p => if p = [2] then .bool else .int .w8
      auxInt := fun p => if p = [1, 0] then 4 else 0, aux := fun _ => none }
    (Oracle.const true) := by
  refine ⟨Oracle.const_boolTyped true, ?_⟩
  simp [GoFV.Rules.Generated.Generic.r_generic_2322, FrameOK, CondMathOK, condMath?, condMathArm,
    condMathOp, condMathFacts, Result.nodes, samePtrVars, sameLeaves, numElem1Vars, size0Vars,
    shiftAmt?, Pat.leafPos, Pat.leafPoss, Pat.rawT, Pat.densT, Pat.denT, emptyStrVars, opVal]
  rule_eval
  refine ⟨by rintro _ _ _ _ rfl rfl rfl rfl; simp, ?_⟩
  simp [sigmaT, Pat.bindsT, Pat.bindssT, List.lookup, Pat.denT]

end GoFV.Proof.Rules
