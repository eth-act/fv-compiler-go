import GoFV.Opt.RewriteCheck
import GoFV.Rules.Generated.Generic

/-!
# Selections of `Phi`s of `SliceMake`s (issue #69)

`generic.rules:1049` (`(SliceLen (Phi (SliceMake _ x _) (SliceMake _ x _))) => x`) and `:1050`
(the capacity) match through a `Phi`, which the term validator treats as an atom (its value is
the `SliceMake` of the edge it was entered along, not a term), so `Rule.SoundT` does not apply;
the checked rewrite takes each instance out of the log and relates the input to the function
with the selection turned `Copy x` (`GoFV.Opt.RewriteCheck.psRel`: the `Phi`'s arguments are
`SliceMake`s with argument `x`, `x` is defined in a strict dominator of the `Phi`'s block, the
shapes are slices and `int64`; refinement: `GoFV.Proof.PhiSel.ps_refines`). The rule-level
obligation `EffectRule.PhiSel` is the shape that makes this per-instance check apply
(`RewriteCheck.psShapeOK`).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- **The obligation of a `Phi` selection rule**: a `SliceLen`/`SliceCap` of a `Phi` with a copy
result (`RewriteCheck.psShapeOK`); each instance is validated by `RewriteCheck.psRel`. -/
def EffectRule.PhiSel (r : Rule) : Prop := GoFV.Opt.RewriteCheck.psShapeOK r = true

/-- `generic.rules:1049`: `(SliceLen (Phi (SliceMake _ x _) (SliceMake _ x _))) => x` -/
theorem r_generic_1049_sound : EffectRule.PhiSel GoFV.Rules.Generated.Generic.r_generic_1049 :=
  rfl

/-- `generic.rules:1050`: `(SliceCap (Phi (SliceMake _ _ x) (SliceMake _ _ x))) => x` -/
theorem r_generic_1050_sound : EffectRule.PhiSel GoFV.Rules.Generated.Generic.r_generic_1050 :=
  rfl

/-- The shape is not vacuous: `generic.rules:1031` (a `SliceLen` of a `SliceMake`) is no `Phi`
selection. -/
example : ¬ EffectRule.PhiSel GoFV.Rules.Generated.Generic.r_generic_1031 := by
  unfold EffectRule.PhiSel; decide

end GoFV.Proof.Rules
