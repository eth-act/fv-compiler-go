import GoFV.Opt.RewriteCheck
import GoFV.Rules.Generated.Generic

/-!
# Nil-check elimination rules (issue #151)

`(NilCheck x:(Op …) _) => x` replaces a root, the nil check, by its pointer. Its obligation is
not a value refinement (`Rule.SoundT`: the nil check is not a term) but that the check cannot
panic, which depends on the instance's pointer. The checked rewrite validates each instance by
nilcheckelim's checker (`GoFV.Opt.RewriteCheck.nilPre`, `GoFV.Opt.NilCheck.nrel`): the pointer
is a `safePtr` seed (an `Addr` or `LocalAddr` with a symbol, a nil check, or `GetG`, whose value
is the environment's `g` allocation `Blk.global "runtime.g"`: it points into an allocation,
`GoFV.Proof.Nil.nn_of_safe`) and the other roots keep their order
(`GoFV.Proof.Nil.refines_of_rel`). The rule-level obligation `EffectRule.NilElim` is the shape
that makes this per-instance check apply: the result is the checked pointer, and the pointer's
op is a `safePtr` seed (`RewriteCheck.nilElimOK`, which the validator also checks).

Not provable this way (the pointer is not a seed): `generic.rules:1367` (`isMalloc` call result:
the contracts do not say that `mallocgc` returns non-nil), `:1384` (dictionary `Arg`: non-nil
only by the compiler's calling convention), `:1376` (`Convert` of `Addr`).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- **The obligation of a nil-check elimination rule**: `(NilCheck x:(Op …) _) => x` with `Op` a
`safePtr` seed (`RewriteCheck.nilElimOK`); each instance is validated by `NilCheck.nrel`. -/
def EffectRule.NilElim (r : Rule) : Prop := GoFV.Opt.RewriteCheck.nilElimOK r = true

/-- `generic.rules:1062`: `(NilCheck ptr:(GetG mem) mem) => ptr` -/
theorem r_generic_1062_sound : EffectRule.NilElim GoFV.Rules.Generated.Generic.r_generic_1062 := rfl

/-- `generic.rules:1375`: `(NilCheck ptr:(Addr {_} (SB)) _) => ptr` -/
theorem r_generic_1375_sound : EffectRule.NilElim GoFV.Rules.Generated.Generic.r_generic_1375 := rfl

/-- `generic.rules:1381`: `(NilCheck ptr:(LocalAddr _ _) _) && warnRule(fe.Debug_checknil(), v, "removed nil check") => ptr` -/
theorem r_generic_1381_sound : EffectRule.NilElim GoFV.Rules.Generated.Generic.r_generic_1381 := rfl

/-- `generic.rules:1388`: `(NilCheck ptr:(NilCheck _ _) _ ) => ptr` -/
theorem r_generic_1388_sound : EffectRule.NilElim GoFV.Rules.Generated.Generic.r_generic_1388 := rfl

/-- Non-vacuity: `:1367` (`isMalloc` call result) does not have the shape. -/
example : GoFV.Opt.RewriteCheck.nilElimOK GoFV.Rules.Generated.Generic.r_generic_1367 = false := rfl

end GoFV.Proof.Rules
