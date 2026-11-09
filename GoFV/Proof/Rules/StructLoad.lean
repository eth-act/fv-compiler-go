import GoFV.Opt.RewriteCheck
import GoFV.Rules.Generated.Generic

variable [GoFV.SSA.Sem.Addrs]

/-!
# Struct-load expansion rules (issue #151)

`(Load <t> _ _) && t.IsStruct() && t.Size() > 0 && CanSSA(t) && !t.IsSIMD() =>
rewriteStructLoad(v)` turns a `Load` of a struct into `StructMake` of fresh field `Load`s at
`OffPtr`s. Its result is computed by a helper, not a pattern, so `Rule.SoundT` does not apply;
the checked rewrite validates each instance (`GoFV.Opt.RewriteCheck.structLoadOK`: the fields
of the `Load`'s aggregate shape, well laid out with every offset inside it, each an `OffPtr` of
the `Load`'s pointer and a `Load` of that at the field's shape from the same memory) and
`GoFV.Proof.Pass.Rewrite.SLFacts.step` proves the expansion refines the `Load` as a term over
the atoms (`GoFV.Proof.Pass.StructLoad.structLoad_ref`, for every memory value). The rule-level
obligation `EffectRule.StructLoad` is the shape that makes this per-instance check apply
(`RewriteCheck.structLoadShapeOK`).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- **The obligation of a struct-load expansion rule**: `(Load …) => rewriteStructLoad(v)`
(`RewriteCheck.structLoadShapeOK`); each instance is validated by `RewriteCheck.structLoadOK`. -/
def EffectRule.StructLoad (r : Rule) : Prop := GoFV.Opt.RewriteCheck.structLoadShapeOK r = true

/-- `generic.rules:974`: `(Load <t> _ _) && t.IsStruct() && t.Size() > 0 && CanSSA(t) && !t.IsSIMD() => rewriteStructLoad(v)` -/
theorem r_generic_974_sound : EffectRule.StructLoad GoFV.Rules.Generated.Generic.r_generic_974 :=
  rfl

/-- Non-vacuity: the array-of-one split `:994` (a pattern result) does not have the shape. -/
example : GoFV.Opt.RewriteCheck.structLoadShapeOK GoFV.Rules.Generated.Generic.r_generic_994 = false :=
  rfl

end GoFV.Proof.Rules
