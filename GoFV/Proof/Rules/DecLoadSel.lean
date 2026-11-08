import GoFV.Proof.Rules.AllSound
import GoFV.Rules.Generated.Dec.Values00

variable [GoFV.SSA.Sem.Addrs]

/-!
# Unconditional selections of a `Load` (issue #17)

`(StructSelect [i] x:(Load <t> ptr mem)) => @x.Block (Load <v.Type> (OffPtr <v.Type.PtrTo()>
[t.FieldOff(int(i))] ptr) mem)` (`dec.rules:141`) and `(ArraySelect [i] x:(Load <t> ptr mem))
=> @x.Block (Load <v.Type> (OffPtr <v.Type.PtrTo()> [t.Elem().Size()*i] ptr) mem)` (`:132`).
Nothing in either rule ties `v`'s type to the selected field's (a `Load` at another shape of the
same bytes need not refine the field), so neither has a `Rule.Sound` proof; the obligation is
`Rule.LoadSel` (`loadSelShape`), and the checked rewrite validates each instance, and only so
(`GoFV.Opt.RewriteCheck.loadSelOK`: field `k` of the `Load`'s aggregate shape is `(o, t)`, `v`
becomes a copy of a fresh `Load` of shape `t` compatible with `v`'s on a fresh `OffPtr [o]` of
the pointer), which `GoFV.Proof.Pass.Rewrite.LSFacts.step` proves refines the selection as a term
over the atoms (`selLoad_ref`). Pass execution witness: `GoFV.Proof.Witness.lsel_checkedRewrite`.
-/

namespace GoFV.Proof.Rules

/-- `dec.rules:132`: `(ArraySelect [i] x:(Load <t> ptr mem)) => @x.Block (Load <v.Type> (OffPtr <v.Type.PtrTo()> [t.Elem().Size()*i] ptr) mem)` -/
theorem r_dec_132_sound : Rule.LoadSel GoFV.Rules.Generated.Dec.r_dec_132 := rfl

/-- `dec.rules:141`: `(StructSelect [i] x:(Load <t> ptr mem)) => @x.Block (Load <v.Type> (OffPtr <v.Type.PtrTo()> [t.FieldOff(int(i))] ptr) mem)` -/
theorem r_dec_141_sound : Rule.LoadSel GoFV.Rules.Generated.Dec.r_dec_141 := rfl

/-- Non-vacuity: the conditional extractors (`dec.rules:135`, a `Rule.Sound` lemma) and the
selections of a `Make` do not have the shape. -/
example : loadSelShape GoFV.Rules.Generated.Dec.r_dec_135 = false := rfl
example : loadSelShape GoFV.Rules.Generated.Dec.r_dec_106 = false := rfl

end GoFV.Proof.Rules
