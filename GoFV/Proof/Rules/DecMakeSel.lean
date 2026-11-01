import GoFV.Proof.Rules.AllSound
import GoFV.Rules.Generated.Dec.Values00
import GoFV.Rules.Generated.Generic.Values12

/-!
# Selections of a variadic `Make` (issue #17)

`(StructSelect [i] x:(StructMake ___)) => x.Args[i]` (`dec.rules:106`, `generic.rules:973`)
makes a selection of a `StructMake` a copy of its argument `i`. The `___` pattern has no
`Rule.Sound` form (`Pat.arityOk`); the obligation is `Rule.MakeSel` (the rule has
`makeSelShape`), and the checked rewrite validates each instance
(`GoFV.Opt.RewriteCheck.makeSelOK`: component `k` of the `StructMake`'s aggregate shape is the
shape of argument `k` and of the selection), which
`GoFV.Proof.Pass.Rewrite.MSFacts.step` proves refines the selection as a term over the atoms
(`select_retype_make_get`). Pass execution witness: `GoFV.Proof.Witness.mks_checkedRewrite`.
-/

namespace GoFV.Proof.Rules

/-- `dec.rules:106`: `(StructSelect [i] x:(StructMake ___)) => x.Args[i]` -/
theorem r_dec_106_sound : Rule.MakeSel GoFV.Rules.Generated.Dec.r_dec_106 := rfl

/-- `generic.rules:973`: `(StructSelect [i] x:(StructMake ___)) => x.Args[i]` -/
theorem r_generic_973_sound : Rule.MakeSel GoFV.Rules.Generated.Generic.r_generic_973 := rfl

/-- Non-vacuity: a selection of a pointer-shaped value (`dec.rules:115`) does not have the
shape. -/
example : makeSelShape GoFV.Rules.Generated.Dec.r_dec_115 = false := rfl

end GoFV.Proof.Rules
