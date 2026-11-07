import GoFV.Proof.Rules.AllSound
import GoFV.Rules.Generated.Generic.Values03
import GoFV.Rules.Generated.Dec.Values00

/-!
# Rule lemmas: an `IMake` of a `StructMake` (issue #69)

`(IMake _typ (StructMake ___)) => imakeOfStructMake(v)` (`generic.rules:981`, `dec.rules:102`)
puts a `struct{*T}` into a direct interface as its field: `v` becomes a copy of a fresh `IMake`
of the struct's first field of non-zero size. The helper is no term the denotation models, so
the obligation is `Rule.IMakeSM` (`imsShape`), and the checked rewrite validates each instance
(`GoFV.Opt.RewriteCheck.imsOK`; refinement: `GoFV.Proof.Pass.Rewrite.IMFacts.step`: the
interface's data word read at its pointer shape from a struct value is `poison`).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- `generic.rules:981`: `(IMake _typ (StructMake ___)) => imakeOfStructMake(v)` -/
theorem r_generic_981_sound : Rule.IMakeSM GoFV.Rules.Generated.Generic.r_generic_981 := rfl

/-- `dec.rules:102`: `(IMake _typ (StructMake ___)) => imakeOfStructMake(v)` -/
theorem r_dec_102_sound : Rule.IMakeSM GoFV.Rules.Generated.Dec.r_dec_102 := rfl

/-- The shape is not vacuous: `generic.rules:1000` (`(IMake _typ (ArrayMake1 val)) => (IMake
_typ val)`) has no `imakeOfStructMake` result. -/
example : ¬ Rule.IMakeSM GoFV.Rules.Generated.Generic.r_generic_1000 := by
  unfold Rule.IMakeSM; decide

end GoFV.Proof.Rules
