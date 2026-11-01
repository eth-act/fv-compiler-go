import GoFV.Opt.RewriteCheck
import GoFV.Rules.Generated.Generic

/-!
# Load-of-Store forwarding rules (issue #151)

`(Load <t1> p1 (Store {t2} p2 x _)) && isSamePtr(p1, p2) && … => x` and its forms through up to
three more `Store`s at addresses `disjoint` from the read replace a `Load` (a term) by the value
a `Store` (a root, an atom of the term denotation) wrote. Their obligation is not a value
refinement (`Rule.SoundT` denotes the `Store` by its register, about which a valuation says
nothing) but that the `Load` reads the stored value back, which depends on the instance: the
checked rewrite validates each instance (`GoFV.Opt.RewriteCheck.fwdPre`, `fwdRel`, `fwdOK`:
through `Store`s at pointers disjoint from the read, `disjointB`, a `Store` at a pointer equal
to the Load's, `samePtrB`; the `Load`, the `Store`'s type and the value have one integer,
boolean or pointer shape, `fwdTyEq`) and `GoFV.Proof.Pass.LoadFwd.fwd_refines` proves the
forwarded function refines its input, under the atom simulation's `MemAtoms` (a `Store`'s
register is the write of its arguments, a `LocalAddr`'s its frame variable). The rule-level
obligation `EffectRule.LoadFwd` is the shape that makes this per-instance check apply
(`RewriteCheck.fwdShapeOK`, which the validator also checks).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- **The obligation of a Load-of-Store forwarding rule**: `(Load _ (Store _ x _)) => x`, also
through up to three more `Store`s, or `(Load _ (Store _ (Const64 [x]) _)) => (Const64F [x'])` and
its converse (`RewriteCheck.fwdShapeOK`); each instance is validated by `RewriteCheck.fwdRel`. -/
def EffectRule.LoadFwd (r : Rule) : Prop := GoFV.Opt.RewriteCheck.fwdShapeOK r = true

/-- `generic.rules:800`: `(Load <t1> p1 (Store {t2} p2 x _)) && isSamePtr(p1, p2) && copyCompatibleType(t1, x.Type) && t1.Size() == t2.Size() => x` -/
theorem r_generic_800_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_800 := rfl

/-- `generic.rules:806`: `(Load <t1> p1 (Store {t2} p2 _ (Store {t3} p3 x _))) && isSamePtr(p1, p3) && … && disjoint(p3, t3.Size(), p2, t2.Size()) => x` -/
theorem r_generic_806_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_806 := rfl

/-- `generic.rules:813`: `(Load <t1> p1 (Store {t2} p2 _ (Store {t3} p3 _ (Store {t4} p4 x _)))) && isSamePtr(p1, p4) && … => x` -/
theorem r_generic_813_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_813 := rfl

/-- `generic.rules:821`: `(Load <t1> p1 (Store {t2} p2 _ (Store {t3} p3 _ (Store {t4} p4 _ (Store {t5} p5 x _))))) && isSamePtr(p1, p5) && … => x` -/
theorem r_generic_821_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_821 := rfl

/-- `generic.rules:830`: `(Load <t1> p1 (Store {t2} p2 (Const64 [x]) _)) && isSamePtr(p1,p2) && t2.Size() == 8 && is64BitFloat(t1) && !math.IsNaN(math.Float64frombits(uint64(x))) => (Const64F [math.Float64frombits(uint64(x))])` -/
theorem r_generic_830_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_830 := rfl

/-- `generic.rules:832`: `(Load <t1> p1 (Store {t2} p2 (Const64F [x]) _)) && isSamePtr(p1,p2) && t2.Size() == 8 && is64BitInt(t1) => (Const64 [int64(math.Float64bits(x))])` -/
theorem r_generic_832_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_832 := rfl

/-- Non-vacuity: the Move forwarding `:827` (a `Load` rebuilt through a `Move`) does not have the
shape. -/
example : GoFV.Opt.RewriteCheck.fwdShapeOK GoFV.Rules.Generated.Generic.r_generic_827 = false := rfl

end GoFV.Proof.Rules
