import GoFV.Opt.RewriteCheck
import GoFV.Rules.Generated.Generic

/-!
# Nil-check elimination rules (issue #151)

`(NilCheck x:(Op …) _) => x` replaces a root, the nil check, by its pointer. Its obligation is
not a value refinement (`Rule.SoundT`: the nil check is not a term) but that the check cannot
panic, which depends on the instance's pointer. The checked rewrite validates each instance by
nilcheckelim's checker with the rewrite passes' seeds (`GoFV.Opt.RewriteCheck.nilPre`,
`GoFV.Opt.NilCheck.nrel true`): the pointer is a `safePtr true` seed (an `Addr` or `LocalAddr`
with a symbol, a nil check, `GetG`, whose value is the environment's `g` allocation
`Blk.global "runtime.g"`, an `OffPtr` or a `Convert` of such a pointer (at a pointer shape
`Convert` is the identity), the `SelectN [0]` of a malloc-family call or a dictionary `Arg`: it
points into an allocation, `GoFV.Proof.Nil.nn_of_safe`, the last two under the rewrite passes'
precondition `Sem.Env.AllocNonNil` and `Sem.DictArgs`) and the other roots keep their order
(`GoFV.Proof.Nil.refinesFrom_of_rel`). The rule-level obligation `EffectRule.NilElim` is the
shape that makes this per-instance check apply: the result is the checked pointer, and the
pointer's op can be a `safePtr true` seed (`RewriteCheck.nilElimOK`, which the validator also
checks).

`(IsNonNil (LocalAddr _ _)) => (ConstBool [true])` (`generic.rules:1691`) has the same kind of
obligation: `LocalAddr` is not a term node, so the rule is validated per instance like the nil
checks (`RuleSet.nilChecks` are also tried on an `IsNonNil`; `nilPre` turns it into
`ConstBool [1]`), and `nrel` takes a pointer-typed `LocalAddr` with a name, or an `Addr` of a
symbol, as non-nil whenever it is evaluated (`NilCheck.nnSeed`, `GoFV.Proof.Nil.nnSeed_reg`).
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

/-- `generic.rules:1376`: `(NilCheck ptr:(Convert (Addr {_} (SB)) _) _) => ptr` -/
theorem r_generic_1376_sound : EffectRule.NilElim GoFV.Rules.Generated.Generic.r_generic_1376 := rfl

/-- `generic.rules:1388`: `(NilCheck ptr:(NilCheck _ _) _ ) => ptr` -/
theorem r_generic_1388_sound : EffectRule.NilElim GoFV.Rules.Generated.Generic.r_generic_1388 := rfl

/-- `generic.rules:1367`: `(NilCheck ptr:(SelectN [0] call:(StaticLECall ___)) _) && isMalloc(call.Aux) && warnRule(fe.Debug_checknil(), v, "removed nil check") => ptr` -/
theorem r_generic_1367_sound : EffectRule.NilElim GoFV.Rules.Generated.Generic.r_generic_1367 := rfl

/-- `generic.rules:1372`: `(NilCheck ptr:(OffPtr (SelectN [0] call:(StaticLECall ___))) _) && isMalloc(call.Aux) && warnRule(fe.Debug_checknil(), v, "removed nil check") => ptr` -/
theorem r_generic_1372_sound : EffectRule.NilElim GoFV.Rules.Generated.Generic.r_generic_1372 := rfl

/-- `generic.rules:1384`: `(NilCheck ptr:(Arg {sym}) _) && isDictArgSym(sym) => ptr` -/
theorem r_generic_1384_sound : EffectRule.NilElim GoFV.Rules.Generated.Generic.r_generic_1384 := rfl

/-- `generic.rules:1691`: `(IsNonNil (LocalAddr _ _)) => (ConstBool [true])`; the `LocalAddr`
is an `NilCheck.nnSeed`, which `nrel` takes as non-nil. -/
theorem r_generic_1691_sound : EffectRule.NilElim GoFV.Rules.Generated.Generic.r_generic_1691 := rfl

end GoFV.Proof.Rules
