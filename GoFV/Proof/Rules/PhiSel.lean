import GoFV.Opt.RewriteCheck
import GoFV.Rules.Generated.Generic

/-!
# `Phi` rules validated per instance: selections of `Phi`s of `SliceMake`s and constant `Phi`s
(issue #69)

`generic.rules:1049` (`(SliceLen (Phi (SliceMake _ x _) (SliceMake _ x _))) => x`) and `:1050`
(the capacity) match through a `Phi`, which the term validator treats as an atom (its value is
the `SliceMake` of the edge it was entered along, not a term), so `Rule.SoundT` does not apply;
the checked rewrite takes each instance out of the log and relates the input to the function
with the selection turned `Copy x` (`GoFV.Opt.RewriteCheck.psRel`: the `Phi`'s arguments are
`SliceMake`s with argument `x`, `x` is defined in a strict dominator of the `Phi`'s block, the
shapes are slices and `int64`; refinement: `GoFV.Proof.PhiSel.ps_refines`).

`generic.rules:782`–`:785` (`(Phi (Const64 [c]) (Const64 [c])) => (Const64 [c])`, the narrower
widths likewise) turn a `Phi` itself into a constant; the checked rewrite relates each instance
by sccp's checker (`GoFV.Opt.RewriteCheck.pcRel`: every argument of the `Phi` is a constant of the
value it becomes; refinement: `GoFV.Proof.PhiConst.pc_refines`).

The rule-level obligation `EffectRule.PhiSel` is the shape that makes one of these per-instance
checks apply (`RewriteCheck.psShapeOK` or `RewriteCheck.pcShapeOK`).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- **The obligation of a `Phi` rule validated per instance**: a `SliceLen`/`SliceCap` of a `Phi`
with a copy result (`RewriteCheck.psShapeOK`), each instance validated by `RewriteCheck.psRel`, or
a `Phi` turned a constant (`RewriteCheck.pcShapeOK`), each instance validated by
`RewriteCheck.pcRel`. -/
def EffectRule.PhiSel (r : Rule) : Prop :=
  (GoFV.Opt.RewriteCheck.psShapeOK r || GoFV.Opt.RewriteCheck.pcShapeOK r) = true

/-- `generic.rules:1049`: `(SliceLen (Phi (SliceMake _ x _) (SliceMake _ x _))) => x` -/
theorem r_generic_1049_sound : EffectRule.PhiSel GoFV.Rules.Generated.Generic.r_generic_1049 :=
  rfl

/-- `generic.rules:1050`: `(SliceCap (Phi (SliceMake _ _ x) (SliceMake _ _ x))) => x` -/
theorem r_generic_1050_sound : EffectRule.PhiSel GoFV.Rules.Generated.Generic.r_generic_1050 :=
  rfl

/-- `generic.rules:782`: `(Phi (Const8 [c]) (Const8 [c])) => (Const8 [c])` -/
theorem r_generic_782_sound : EffectRule.PhiSel GoFV.Rules.Generated.Generic.r_generic_782 :=
  rfl

/-- `generic.rules:783`: `(Phi (Const16 [c]) (Const16 [c])) => (Const16 [c])` -/
theorem r_generic_783_sound : EffectRule.PhiSel GoFV.Rules.Generated.Generic.r_generic_783 :=
  rfl

/-- `generic.rules:784`: `(Phi (Const32 [c]) (Const32 [c])) => (Const32 [c])` -/
theorem r_generic_784_sound : EffectRule.PhiSel GoFV.Rules.Generated.Generic.r_generic_784 :=
  rfl

/-- `generic.rules:785`: `(Phi (Const64 [c]) (Const64 [c])) => (Const64 [c])` -/
theorem r_generic_785_sound : EffectRule.PhiSel GoFV.Rules.Generated.Generic.r_generic_785 :=
  rfl

/-- The shape is not vacuous: `generic.rules:1031` (a `SliceLen` of a `SliceMake`) is no `Phi`
selection, and `generic.rules:1068` (a `Phi` of `Not`s turned `Not (Phi …)`) no constant `Phi`. -/
example : ¬ EffectRule.PhiSel GoFV.Rules.Generated.Generic.r_generic_1031 := by
  unfold EffectRule.PhiSel; decide

example : ¬ EffectRule.PhiSel GoFV.Rules.Generated.Generic.r_generic_1068 := by
  unfold EffectRule.PhiSel; decide

end GoFV.Proof.Rules
