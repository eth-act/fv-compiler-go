import GoFV.Opt.RewriteCheck
import GoFV.Rules.Generated.Generic
import GoFV.Rules.Generated.Dec

/-!
# Struct-store split rules (issues #151, #17)

`(Store _ (StructMake ___) _) => rewriteStructStore(v)` replaces a `Store` of a struct (a root)
by a chain of fresh field `Store`s at `OffPtr`s, and the `Store` by `Copy` of the chain's last.
Its result is computed by a helper, not a pattern, so `Rule.SoundT` does not apply; the checked
rewrite takes each instance out of the log and relates the input to the function with the
split applied (`GoFV.Opt.RewriteCheck.ssRel`; refinement: `GoFV.Proof.Pass.StructStore.ss_refines`).
A `Store` rule with a built result (the decompose rules of a `Store` of a builtin `Make`,
`GoFV/Proof/Rules/DecStore.lean`) splits the `Store` in place and is validated alike.
The rule-level obligation `EffectRule.StructStore` is the shape that makes this per-instance
check apply (`RewriteCheck.structStoreShapeOK`).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- **The obligation of a struct-store split rule**: `(Store …) => rewriteStructStore(v)` or a
`Store` rule with a built result in `v`'s block (`RewriteCheck.structStoreShapeOK`); each
instance is validated by `RewriteCheck.ssRel`. -/
def EffectRule.StructStore (r : Rule) : Prop := GoFV.Opt.RewriteCheck.structStoreShapeOK r = true

/-- `generic.rules:975`: `(Store _ (StructMake ___) _) => rewriteStructStore(v)` -/
theorem r_generic_975_sound : EffectRule.StructStore GoFV.Rules.Generated.Generic.r_generic_975 :=
  rfl

/-- `generic.rules:997`: `(Store dst (ArrayMake1 e) mem) => (Store {e.Type} dst e mem)` (an
in-place split into its one element's `Store`, as `dec.rules:129`) -/
theorem r_generic_997_sound : EffectRule.StructStore GoFV.Rules.Generated.Generic.r_generic_997 :=
  rfl

/-- Non-vacuity: the size-0 store elimination `dec.rules:10` (`=> mem`) does not have the shape. -/
example : GoFV.Opt.RewriteCheck.structStoreShapeOK GoFV.Rules.Generated.Dec.r_dec_10 = false :=
  rfl

end GoFV.Proof.Rules
