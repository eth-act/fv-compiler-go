import GoFV.Opt.RewriteCheck
import GoFV.Rules.Generated.Generic

/-!
# Struct-store split rules (issue #151)

`(Store _ (StructMake ___) _) => rewriteStructStore(v)` replaces a `Store` of a struct (a root)
by a chain of fresh field `Store`s at `OffPtr`s, and the `Store` by `Copy` of the chain's last.
Its result is computed by a helper, not a pattern, so `Rule.SoundT` does not apply; the checked
rewrite takes each instance out of the log and relates the input to the function with the
split applied (`GoFV.Opt.RewriteCheck.ssRel`; refinement: `GoFV.Proof.Pass.StructStore.ss_refines`).
The rule-level obligation `EffectRule.StructStore` is the shape that makes this per-instance
check apply (`RewriteCheck.structStoreShapeOK`).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- **The obligation of a struct-store split rule**: `(Store …) => rewriteStructStore(v)`
(`RewriteCheck.structStoreShapeOK`); each instance is validated by `RewriteCheck.ssRel`. -/
def EffectRule.StructStore (r : Rule) : Prop := GoFV.Opt.RewriteCheck.structStoreShapeOK r = true

/-- `generic.rules:975`: `(Store _ (StructMake ___) _) => rewriteStructStore(v)` -/
theorem r_generic_975_sound : EffectRule.StructStore GoFV.Rules.Generated.Generic.r_generic_975 :=
  rfl

/-- Non-vacuity: the array-of-one store split `:986` (a pattern result) does not have the shape. -/
example : GoFV.Opt.RewriteCheck.structStoreShapeOK GoFV.Rules.Generated.Generic.r_generic_986 = false :=
  rfl

end GoFV.Proof.Rules
