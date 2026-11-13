import GoFV.Opt.RewriteCheck
import GoFV.Rules.Generated.Generic

variable [GoFV.SSA.Sem.Addrs]

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
of a `growslice` result `(SliceLen (SelectN [0] (StaticLECall _ newLen:(Const64) …))) => newLen`;
or a folded `ifaceeq`/`efaceeq` call `(StaticLECall {f} d x y mem) && … => (MakeResult (EqPtr x
y) mem)` and a selection of a `MakeResult` `(SelectN [n] m:(MakeResult ___)) => m.Args[n]`; or
a load from a read-only symbol `(Load <IntN> (Addr {s} (SB)) _) && symIsRO(s) => (ConstN [readN(s,
0)])`, validated as the fixed loads (`RewriteCheck.fixedOK`)
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

/-- `generic.rules:919`: `(Store {t1} p1 (Load <t2> p2 mem) mem) && isSamePtr(p1, p2) && t2.Size() == t1.Size() => mem` (issue #69: the write-back of a narrow integer or `bool` the `Load` read, `RewriteCheck.writeBackOK`; false at the word shapes, whose reloaded pointer stores back as its address bytes) -/
theorem r_generic_919_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_919 := rfl

/-- `generic.rules:924`: `(Store {t1} p1 (Load <t2> p2 oldmem) mem:(Store {t3} p3 _ oldmem)) && isSamePtr(p1, p2) && t2.Size() == t1.Size() && disjoint(p1, t1.Size(), p3, t3.Size()) => mem` (issue #69: `:919` through a disjoint `Store`, `RewriteCheck.wbChain`; false at the word shapes) -/
theorem r_generic_924_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_924 := rfl

/-- `generic.rules:930`: `(Store {t1} p1 (Load <t2> p2 oldmem) mem:(Store {t3} p3 _ (Store {t4} p4 _ oldmem))) && isSamePtr(p1, p2) && t2.Size() == t1.Size() && disjoint(p1, t1.Size(), p3, t3.Size()) && disjoint(p1, t1.Size(), p4, t4.Size()) => mem` (issue #69: `:919` through two disjoint `Store`s; false at the word shapes) -/
theorem r_generic_930_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_930 := rfl

/-- `generic.rules:937`: `(Store {t1} p1 (Load <t2> p2 oldmem) mem:(Store {t3} p3 _ (Store {t4} p4 _ (Store {t5} p5 _ oldmem)))) && isSamePtr(p1, p2) && t2.Size() == t1.Size() && disjoint(p1, t1.Size(), p3, t3.Size()) && disjoint(p1, t1.Size(), p4, t4.Size()) && disjoint(p1, t1.Size(), p5, t5.Size()) => mem` (issue #69: `:919` through three disjoint `Store`s; false at the word shapes) -/
theorem r_generic_937_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_937 := rfl

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

/-- `generic.rules:2159`: `(Zero {t} [s] dst1 vardef:(VarDef (Zero {t} [s] dst2 _))) && isSamePtr(dst1, dst2) => vardef` (a `Zero` of zero bytes, `RewriteCheck.zeroChain` through a `VarDef` of a variable that is not a `PAUTO`, `Sem.varDefMem`) -/
theorem r_generic_2159_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2159 := rfl

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

/-- `generic.rules:2131`: `(SelectN [1] (StaticCall {sym} _ newLen:(Const64) _ _ _ _)) && v.Type.IsInteger() && (isSameCall(sym, "runtime.growslice") || isSameCall(sym, "runtime.growsliceNoAlias")) => newLen` (issue #69: the post-`expand calls` form of `:2128`, `RewriteCheck.growPOK`) -/
theorem r_generic_2131_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2131 := rfl

/-- `generic.rules:842`: `(Load <t1> op:(OffPtr [o1] p1) (Store {t2} p2 _ mem:(Zero [n] p3 _))) && o1 >= 0 && o1+t1.Size() <= n && isSamePtr(p1, p3) && CanSSA(t1) && disjoint(op, t1.Size(), p2, t2.Size()) => @mem.Block (Load <t1> (OffPtr <op.Type> [o1] p3) mem)` (issue #69: the Load reads the `Zero`'s bytes through the disjoint `Store`, `RewriteCheck.fwdSepOK`) -/
theorem r_generic_842_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_842 := rfl

/-- `generic.rules:851`: `(Load <t1> op:(OffPtr [o1] p1) (Store {t2} p2 _ (Store {t3} p3 _ mem:(Zero [n] p4 _)))) && … => @mem.Block (Load <t1> (OffPtr <op.Type> [o1] p4) mem)` -/
theorem r_generic_851_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_851 := rfl

/-- `generic.rules:862`: `(Load <t1> op:(OffPtr [o1] p1) (Store {t2} p2 _ (Store {t3} p3 _ (Store {t4} p4 _ mem:(Zero [n] p5 _))))) && … => @mem.Block (Load <t1> (OffPtr <op.Type> [o1] p5) mem)` -/
theorem r_generic_862_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_862 := rfl

/-- `generic.rules:875`: `(Load <t1> op:(OffPtr [o1] p1) (Store {t2} p2 _ (Store {t3} p3 _ (Store {t4} p4 _ (Store {t5} p5 _ mem:(Zero [n] p6 _)))))) && … => @mem.Block (Load <t1> (OffPtr <op.Type> [o1] p6) mem)` -/
theorem r_generic_875_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_875 := rfl

/-- `generic.rules:882`: `(Load <t1> (OffPtr [o] p1) (Zero [n] p2 _)) && t1.IsBoolean() && isSamePtr(p1, p2) && n >= o + 1 => (ConstBool [false])` (issue #69: the Load reads zero bytes, `RewriteCheck.fwdZeroOK`) -/
theorem r_generic_882_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_882 := rfl

/-- `generic.rules:887`: `(Load <t1> (OffPtr [o] p1) (Zero [n] p2 _)) && is8BitInt(t1) && isSamePtr(p1, p2) && n >= o + 1 => (Const8 [0])` -/
theorem r_generic_887_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_887 := rfl

/-- `generic.rules:892`: `(Load <t1> (OffPtr [o] p1) (Zero [n] p2 _)) && is16BitInt(t1) && isSamePtr(p1, p2) && n >= o + 2 => (Const16 [0])` -/
theorem r_generic_892_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_892 := rfl

/-- `generic.rules:897`: `(Load <t1> (OffPtr [o] p1) (Zero [n] p2 _)) && is32BitInt(t1) && isSamePtr(p1, p2) && n >= o + 4 => (Const32 [0])` -/
theorem r_generic_897_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_897 := rfl

/-- `generic.rules:902`: `(Load <t1> (OffPtr [o] p1) (Zero [n] p2 _)) && is64BitInt(t1) && isSamePtr(p1, p2) && n >= o + 8 => (Const64 [0])` -/
theorem r_generic_902_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_902 := rfl

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

/-- `generic.rules:1564`: `(Load <typ.Int8> sptr:(Addr {scon} (SB)) mem) && symIsRO(scon) => (Const8 <typ.Int8> [int8(read8(scon,0))])` (issue #69: the read from the read-only symbol's allocation, `RewriteCheck.fixedOK`, under `Sem.RoImage`, as the fixed loads) -/
theorem r_generic_1564_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1564 := rfl

/-- `generic.rules:1572`: `(Load <typ.Int16> sptr:(Addr {scon} (SB)) mem) && symIsRO(scon) => (Const16 <typ.Int16> [int16(read16(scon,0,config.ctxt.Arch.ByteOrder))])` -/
theorem r_generic_1572_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1572 := rfl

/-- `generic.rules:1580`: `(Load <typ.Int32> sptr:(Addr {scon} (SB)) mem) && symIsRO(scon) => (Const32 <typ.Int32> [int32(read32(scon,0,config.ctxt.Arch.ByteOrder))])` -/
theorem r_generic_1580_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1580 := rfl

/-- `generic.rules:1588`: `(Load <typ.Int64> sptr:(Addr {scon} (SB)) mem) && symIsRO(scon) => (Const64 <typ.Int64> [int64(read64(scon,0,config.ctxt.Arch.ByteOrder))])` -/
theorem r_generic_1588_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1588 := rfl

/-- `generic.rules:2279`: `(StaticLECall {f} typ_ x y mem) && isSameCall(f, "runtime.efaceeq") && isDirectAndComparableType(typ_) && clobber(v) => (MakeResult (EqPtr x y) mem)` (issues #69, #189: the call's descriptor an `Addr` of a type symbol of the precondition's list, through `ITab (IMake …)` and copies, `RewriteCheck.eqCallOK`; it returns `x == y` under `Sem.Env.IfaceEq`) -/
theorem r_generic_2279_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2279 := rfl

/-- `generic.rules:2287`: `(StaticLECall {f} itab x y mem) && isSameCall(f, "runtime.ifaceeq") && isDirectAndComparableIface(itab) && clobber(v) => (MakeResult (EqPtr x y) mem)` (the itab symbols; the `ConstNil` and `Phi` descriptors of `isDirectAndComparableIface` are rejected) -/
theorem r_generic_2287_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_2287 := rfl

/-- `generic.rules:1343`: `(SelectN [n] m:(MakeResult ___)) => m.Args[n]` (each instance's tuple
type checked, `RewriteCheck.selMROK`; a selection of a call folded in the same layer stays a
selection, `LoadFwd.selDC_den`) -/
theorem r_generic_1343_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1343 := rfl

/-! Pointer comparisons folded to a constant (issue #69: the comparison `RewriteCheck.ptrCmp?`
tells, `RewriteCheck.ptrCmpOK`, `LoadFwd.ptrCmp_den`) -/

/-- `generic.rules:1649`: `(EqPtr (Addr {x} _) (OffPtr [o] (Addr {y} _))) => (ConstBool [x == y && o == 0])` -/
theorem r_generic_1649_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1649 := rfl

/-- `generic.rules:1650`: `(EqPtr (OffPtr [o1] (Addr {x} _)) (OffPtr [o2] (Addr {y} _))) => (ConstBool [x == y && o1 == o2])` -/
theorem r_generic_1650_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1650 := rfl

/-- `generic.rules:1652`: `(NeqPtr (Addr {x} _) (OffPtr [o] (Addr {y} _))) => (ConstBool [x != y || o != 0])` -/
theorem r_generic_1652_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1652 := rfl

/-- `generic.rules:1653`: `(NeqPtr (OffPtr [o1] (Addr {x} _)) (OffPtr [o2] (Addr {y} _))) => (ConstBool [x != y || o1 != o2])` -/
theorem r_generic_1653_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1653 := rfl

/-- `generic.rules:1654`: `(EqPtr (LocalAddr {x} _ _) (LocalAddr {y} _ _)) => (ConstBool [x == y])` -/
theorem r_generic_1654_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1654 := rfl

/-- `generic.rules:1655`: `(EqPtr (LocalAddr {x} _ _) (OffPtr [o] (LocalAddr {y} _ _))) => (ConstBool [x == y && o == 0])` -/
theorem r_generic_1655_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1655 := rfl

/-- `generic.rules:1656`: `(EqPtr (OffPtr [o1] (LocalAddr {x} _ _)) (OffPtr [o2] (LocalAddr {y} _ _))) => (ConstBool [x == y && o1 == o2])` -/
theorem r_generic_1656_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1656 := rfl

/-- `generic.rules:1657`: `(NeqPtr (LocalAddr {x} _ _) (LocalAddr {y} _ _)) => (ConstBool [x != y])` -/
theorem r_generic_1657_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1657 := rfl

/-- `generic.rules:1658`: `(NeqPtr (LocalAddr {x} _ _) (OffPtr [o] (LocalAddr {y} _ _))) => (ConstBool [x != y || o != 0])` -/
theorem r_generic_1658_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1658 := rfl

/-- `generic.rules:1659`: `(NeqPtr (OffPtr [o1] (LocalAddr {x} _ _)) (OffPtr [o2] (LocalAddr {y} _ _))) => (ConstBool [x != y || o1 != o2])` -/
theorem r_generic_1659_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1659 := rfl

/-- `generic.rules:1660`: `(EqPtr (OffPtr [o1] p1) p2) && isSamePtr(p1, p2) => (ConstBool [o1 == 0])` -/
theorem r_generic_1660_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1660 := rfl

/-- `generic.rules:1661`: `(NeqPtr (OffPtr [o1] p1) p2) && isSamePtr(p1, p2) => (ConstBool [o1 != 0])` -/
theorem r_generic_1661_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1661 := rfl

/-- `generic.rules:1662`: `(EqPtr (OffPtr [o1] p1) (OffPtr [o2] p2)) && isSamePtr(p1, p2) => (ConstBool [o1 == o2])` -/
theorem r_generic_1662_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1662 := rfl

/-- `generic.rules:1663`: `(NeqPtr (OffPtr [o1] p1) (OffPtr [o2] p2)) && isSamePtr(p1, p2) => (ConstBool [o1 != o2])` -/
theorem r_generic_1663_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1663 := rfl

/-- `generic.rules:1666`: `(EqPtr (Convert (Addr {x} _) _) (Addr {y} _)) => (ConstBool [x==y])` -/
theorem r_generic_1666_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1666 := rfl

/-- `generic.rules:1667`: `(NeqPtr (Convert (Addr {x} _) _) (Addr {y} _)) => (ConstBool [x!=y])` -/
theorem r_generic_1667_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1667 := rfl

/-- `generic.rules:1669`: `(EqPtr (LocalAddr _ _) (Addr _)) => (ConstBool [false])` -/
theorem r_generic_1669_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1669 := rfl

/-- `generic.rules:1670`: `(EqPtr (OffPtr (LocalAddr _ _)) (Addr _)) => (ConstBool [false])` -/
theorem r_generic_1670_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1670 := rfl

/-- `generic.rules:1671`: `(EqPtr (LocalAddr _ _) (OffPtr (Addr _))) => (ConstBool [false])` -/
theorem r_generic_1671_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1671 := rfl

/-- `generic.rules:1672`: `(EqPtr (OffPtr (LocalAddr _ _)) (OffPtr (Addr _))) => (ConstBool [false])` -/
theorem r_generic_1672_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1672 := rfl

/-- `generic.rules:1673`: `(NeqPtr (LocalAddr _ _) (Addr _)) => (ConstBool [true])` -/
theorem r_generic_1673_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1673 := rfl

/-- `generic.rules:1674`: `(NeqPtr (OffPtr (LocalAddr _ _)) (Addr _)) => (ConstBool [true])` -/
theorem r_generic_1674_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1674 := rfl

/-- `generic.rules:1675`: `(NeqPtr (LocalAddr _ _) (OffPtr (Addr _))) => (ConstBool [true])` -/
theorem r_generic_1675_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1675 := rfl

/-- `generic.rules:1676`: `(NeqPtr (OffPtr (LocalAddr _ _)) (OffPtr (Addr _))) => (ConstBool [true])` -/
theorem r_generic_1676_sound : EffectRule.LoadFwd GoFV.Rules.Generated.Generic.r_generic_1676 := rfl

/-- Non-vacuity: the struct-load expansion `:974` (`(Load <t> _ _) && t.IsStruct() && … =>
rewriteStructLoad(v)`) and the `Store` rule `:997` (`(Store dst (ArrayMake1 e) mem) => (Store
{e.Type} dst e mem)`, a changed write) do not have the shape. -/
example : GoFV.Opt.RewriteCheck.fwdShapeOK GoFV.Rules.Generated.Generic.r_generic_974 = false := rfl
example : GoFV.Opt.RewriteCheck.fwdShapeOK GoFV.Rules.Generated.Generic.r_generic_997 = false := rfl

end GoFV.Proof.Rules
