import GoFV.Opt.RewriteCheck
import GoFV.Rules.Generated.Generic

/-!
# Load-of-Store forwarding rules (issue #151)

`(Load <t1> p1 (Store {t2} p2 x _)) && isSamePtr(p1, p2) && … => x` replaces a `Load` (a term)
by the value a `Store` (a root, an atom of the term denotation) wrote. Its obligation is not a
value refinement (`Rule.SoundT` denotes the `Store` by its register, about which a valuation
says nothing) but that the `Load` reads the stored value back, which depends on the instance:
the checked rewrite validates each instance (`GoFV.Opt.RewriteCheck.fwdPre`, `fwdRel`, `fwdOK`:
the two pointers evaluate equally, `samePtrB`; the `Load`, the `Store`'s type and the value have
one integer, boolean or pointer shape) and `GoFV.Proof.Pass.LoadFwd.fwd_refines` proves the
forwarded function refines its input, under the atom simulation's `MemAtoms` (a `Store`'s
register is the write of its arguments). The rule-level obligation `EffectRule.LoadFwd` is the
shape that makes this per-instance check apply (`RewriteCheck.fwdShapeOK`, which the validator
also checks).

Not yet: `generic.rules:806`, `:813`, `:821` read through further `Store`s, which needs their
disjointness on the instance.
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- **The obligation of a Load-of-Store forwarding rule**: `(Load _ (Store _ x _)) => x`
(`RewriteCheck.fwdShapeOK`); each instance is validated by `RewriteCheck.fwdRel`. -/
def EffectRule.LoadFwd (r : Rule) : Prop := GoFV.Opt.RewriteCheck.fwdShapeOK r = true

/-- `generic.rules:800`: `(Load <t1> p1 (Store {t2} p2 x _)) && isSamePtr(p1, p2) && copyCompatibleType(t1, x.Type) && t1.Size() == t2.Size() => x` -/
theorem r_generic_800_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_800 := rfl

/-- Non-vacuity: `:806` (through two `Store`s) does not have the shape. -/
example : GoFV.Opt.RewriteCheck.fwdShapeOK GoFV.Rules.Generated.Generic.r_generic_806 = false := rfl

end GoFV.Proof.Rules
