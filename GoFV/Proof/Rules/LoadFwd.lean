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
to the Load's, `samePtrB`; the `Load`, the `Store`'s type and the value have one shape that
reads back what was written, `fwdTyEq`: scalars, strings, slices and nested structs of them)
and `GoFV.Proof.Pass.LoadFwd.fwd_refines` proves the
forwarded function refines its input, under the atom simulation's `MemAtoms` (a `Store`'s
register is the write of its arguments, a `LocalAddr`'s its frame variable). The rule-level
obligation `EffectRule.LoadFwd` is the shape that makes this per-instance check apply
(`RewriteCheck.fwdShapeOK`, which the validator also checks).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- **The obligation of a Load-of-Store forwarding rule**: `(Load _ (Store _ x _)) => x`, also
through up to three more `Store`s, `(Load _ (Store _ (Const64 [x]) _)) => (Const64F [x'])` and
its converse, or `(Load (OffPtr [o] _) (Move _ src mem)) => @move.Block (Load (OffPtr [o] src)
mem)`; or a dropped identity write `(Store _ _ mem) => mem`, `(Zero _ mem) => mem`; or the length
of a `growslice` result `(SliceLen (SelectN [0] (StaticLECall _ newLen:(Const64) …))) => newLen`
(`RewriteCheck.fwdShapeOK`); each instance is validated by `RewriteCheck.fwdRel`. -/
def EffectRule.LoadFwd (r : Rule) : Prop := GoFV.Opt.RewriteCheck.fwdShapeOK r = true

/-- `generic.rules:800`: `(Load <t1> p1 (Store {t2} p2 x _)) && isSamePtr(p1, p2) && copyCompatibleType(t1, x.Type) && t1.Size() == t2.Size() => x` -/
theorem r_generic_800_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_800 := rfl

/-- `generic.rules:806`: `(Load <t1> p1 (Store {t2} p2 _ (Store {t3} p3 x _))) && isSamePtr(p1, p3) && … && disjoint(p3, t3.Size(), p2, t2.Size()) => x` -/
theorem r_generic_806_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_806 := rfl

/-- `generic.rules:813`: `(Load <t1> p1 (Store {t2} p2 _ (Store {t3} p3 _ (Store {t4} p4 x _)))) && isSamePtr(p1, p4) && … => x` -/
theorem r_generic_813_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_813 := rfl

/-- `generic.rules:821`: `(Load <t1> p1 (Store {t2} p2 _ (Store {t3} p3 _ (Store {t4} p4 _ (Store {t5} p5 x _))))) && isSamePtr(p1, p5) && … => x` -/
theorem r_generic_821_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_821 := rfl

/-- `generic.rules:827`: `(Load <t1> op:(OffPtr [o1] p1) move:(Move [n] p2 src mem)) && o1 >= 0 && o1+t1.Size() <= n && isSamePtr(p1, p2) && !isVolatile(src) => @move.Block (Load <t1> (OffPtr <op.Type> [o1] src) mem)` -/
theorem r_generic_827_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_827 := rfl

/-- `generic.rules:830`: `(Load <t1> p1 (Store {t2} p2 (Const64 [x]) _)) && isSamePtr(p1,p2) && t2.Size() == 8 && is64BitFloat(t1) && !math.IsNaN(math.Float64frombits(uint64(x))) => (Const64F [math.Float64frombits(uint64(x))])` -/
theorem r_generic_830_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_830 := rfl

/-- `generic.rules:832`: `(Load <t1> p1 (Store {t2} p2 (Const64F [x]) _)) && isSamePtr(p1,p2) && t2.Size() == 8 && is64BitInt(t1) => (Const64 [int64(math.Float64bits(x))])` -/
theorem r_generic_832_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_832 := rfl

/-- `generic.rules:943`: `(Store {t} (OffPtr [o] p1) x mem:(Zero [n] p2 _)) && isConstZero(x) && o >= 0 && t.Size() + o <= n && isSamePtr(p1, p2) => mem` -/
theorem r_generic_943_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_943 := rfl

/-- `generic.rules:948`: `(Store {t1} op:(OffPtr [o1] p1) x mem:(Store {t2} p2 _ (Zero [n] p3 _))) && isConstZero(x) && … && disjoint(op, t1.Size(), p2, t2.Size()) => mem` -/
theorem r_generic_948_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_948 := rfl

/-- `generic.rules:954`: `(Store {t1} op:(OffPtr [o1] p1) x mem:(Store {t2} p2 _ (Store {t3} p3 _ (Zero [n] p4 _)))) && isConstZero(x) && … => mem` -/
theorem r_generic_954_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_954 := rfl

/-- `generic.rules:961`: `(Store {t1} op:(OffPtr [o1] p1) x mem:(Store {t2} p2 _ (Store {t3} p3 _ (Store {t4} p4 _ (Zero [n] p5 _))))) && isConstZero(x) && … => mem` -/
theorem r_generic_961_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_961 := rfl

/-- `generic.rules:1005`: `(Store _ (Empty) mem) => mem` -/
theorem r_generic_1005_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1005 := rfl

/-- `generic.rules:2158`: `(Zero {t} [s] dst1 zero:(Zero {t} [s] dst2 _)) && isSamePtr(dst1, dst2) => zero` -/
theorem r_generic_2158_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2158 := rfl

/-- `generic.rules:1352`: `(Zero (SelectN [0] call:(StaticLECall ___)) mem:(SelectN [1] call)) && isMalloc(call.Aux) => mem` (issue #69: a `Zero` of zero bytes, `RewriteCheck.zeroChain` from a
fresh zeroed allocation, `RewriteCheck.freshCall`, under `Sem.Env.AllocZero`) -/
theorem r_generic_1352_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1352 := rfl

/-- `generic.rules:1357`: `(Store (SelectN [0] call:(StaticLECall ___)) x mem:(SelectN [1] call)) && isConstZero(x) && isMalloc(call.Aux) => mem` -/
theorem r_generic_1357_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1357 := rfl

/-- `generic.rules:1362`: `(Store (OffPtr (SelectN [0] call:(StaticLECall ___))) x mem:(SelectN [1] call)) && isConstZero(x) && isMalloc(call.Aux) => mem` -/
theorem r_generic_1362_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1362 := rfl

/-- `generic.rules:2146`: `(Move {t1} [s] dst tmp1 midmem:(Move {t2} [s] tmp2 src _)) && … &&
isSamePtr(tmp1, tmp2) && … && disjoint(src, s, tmp2, s) && … => (Move {t1} [s] dst src midmem)` -/
theorem r_generic_2146_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2146 := rfl

/-- `generic.rules:2155`: `(Move {t1} [s] dst tmp1 midmem:(VarDef (Move {t2} [s] tmp2 src _))) &&
… => (Move {t1} [s] dst src midmem)` -/
theorem r_generic_2155_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2155 := rfl

/-- `generic.rules:2128`: `(SliceLen (SelectN [0] (StaticLECall {sym} _ newLen:(Const64) _ _ _ _))) && (isSameCall(sym, "runtime.growslice") || isSameCall(sym, "runtime.growsliceNoAlias")) => newLen` -/
theorem r_generic_2128_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2128 := rfl

/-- `generic.rules:2251`: `(Load (Addr {s} sb) _) && isFixedLoad(v, s, 0) => rewriteFixedLoad(v, s, sb, 0)` (issue #69: the read from the read-only symbol's allocation, `RewriteCheck.fixedOK`,
under `Sem.RoImage`) -/
theorem r_generic_2251_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2251 := rfl

/-- `generic.rules:2255`: `(Load (OffPtr [off] (Addr {s} sb) ) _) && isFixedLoad(v, s, off) => rewriteFixedLoad(v, s, sb, off)` -/
theorem r_generic_2255_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2255 := rfl

/-- `generic.rules:2252`: `(Load (Convert (Addr {s} sb) _) _) && isFixedLoad(v, s, 0) => rewriteFixedLoad(v, s, sb, 0)` (`fixedOK` follows the `Convert` by `RewriteCheck.wordStep?`) -/
theorem r_generic_2252_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2252 := rfl

/-- `generic.rules:2253`: `(Load (ITab (IMake (Addr {s} sb) _)) _) && isFixedLoad(v, s, 0) => rewriteFixedLoad(v, s, sb, 0)` (through `ITab (IMake …)`, `wordStep?`) -/
theorem r_generic_2253_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2253 := rfl

/-- `generic.rules:2254`: `(Load (ITab (IMake (Convert (Addr {s} sb) _) _)) _) && isFixedLoad(v, s, 0) => rewriteFixedLoad(v, s, sb, 0)` -/
theorem r_generic_2254_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2254 := rfl

/-- `generic.rules:2256`: `(Load (OffPtr [off] (Convert (Addr {s} sb) _)) _) && isFixedLoad(v, s, off) => rewriteFixedLoad(v, s, sb, off)` -/
theorem r_generic_2256_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2256 := rfl

/-- `generic.rules:2257`: `(Load (OffPtr [off] (ITab (IMake (Addr {s} sb) _))) _) && isFixedLoad(v, s, off) => rewriteFixedLoad(v, s, sb, off)` -/
theorem r_generic_2257_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2257 := rfl

/-- `generic.rules:2258`: `(Load (OffPtr [off] (ITab (IMake (Convert (Addr {s} sb) _) _))) _) && isFixedLoad(v, s, off) => rewriteFixedLoad(v, s, sb, off)` -/
theorem r_generic_2258_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2258 := rfl

/-- Non-vacuity: the Load-from-`Zero` rule `:842` (a `Load` rebuilt through a `Store` over a
`Zero`) and the `Store` rule `:997` (`(Store dst (ArrayMake1 e) mem) => (Store {e.Type} dst e
mem)`, a changed write) do not have the shape. -/
example : GoFV.Opt.RewriteCheck.fwdShapeOK GoFV.Rules.Generated.Generic.r_generic_842 = false := rfl
example : GoFV.Opt.RewriteCheck.fwdShapeOK GoFV.Rules.Generated.Generic.r_generic_997 = false := rfl

end GoFV.Proof.Rules
