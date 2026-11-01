import GoFV.Proof.Rules.AllSound
import GoFV.Rules.Generated.Dec.Values00
import GoFV.Rules.Generated.Generic.Values12

/-!
# Selections of a variadic `Make` (issue #17)

`(StructSelect [i] x:(StructMake ___)) => x.Args[i]` (`dec.rules:106`, `generic.rules:973`)
makes a selection of a `StructMake` a copy of its argument `i`. The `___` pattern has no
`Rule.Sound` form (`Pat.arityOk`); the obligation is `Rule.MakeSel` (the rule has
`makeSelShape`, a selection of a `Make` with a copy result, and a `___`), and the checked
rewrite validates each instance (`GoFV.Opt.RewriteCheck.makeSelOK`: component `k` of the
`Make`'s aggregate shape is the shape of argument `k` and of the selection, or argument `k` is
an `Addr` under word shapes), which `GoFV.Proof.Pass.Rewrite.MSFacts.step` proves refines the
selection as a term over the atoms (`select_retype_make_get`). The selections of a `Make` with
a `Rule.Sound` lemma (`Dec.lean`) are tried per instance first too. Pass execution witness:
`GoFV.Proof.Witness.mks_checkedRewrite`.
-/

namespace GoFV.Proof.Rules

/-- `dec.rules:106`: `(StructSelect [i] x:(StructMake ___)) => x.Args[i]` -/
theorem r_dec_106_sound : Rule.MakeSel GoFV.Rules.Generated.Dec.r_dec_106 := ⟨rfl, rfl⟩

/-- `generic.rules:973`: `(StructSelect [i] x:(StructMake ___)) => x.Args[i]` -/
theorem r_generic_973_sound : Rule.MakeSel GoFV.Rules.Generated.Generic.r_generic_973 :=
  ⟨rfl, rfl⟩

/-- Non-vacuity: a selection of a pointer-shaped value (`dec.rules:115`) does not have the
shape, and `(ITab (IMake itab _)) => itab` (`dec.rules:82`) has a `Rule.Sound` form. -/
example : makeSelShape GoFV.Rules.Generated.Dec.r_dec_115 = false := rfl
example : ¬ Rule.MakeSel GoFV.Rules.Generated.Dec.r_dec_82 := fun h => by
  have := h.2; revert this; decide

end GoFV.Proof.Rules
