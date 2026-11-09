import GoFV.Proof.Rules.StructStore

variable [GoFV.SSA.Sem.Addrs]

/-!
# Decompose rules of a `Store` of a composite (issue #17)

`dec.rules:23 :35 :51 :72 :93 :129` split a `Store` of a builtin `Make` (complex, string, slice,
interface, `[1]T`) into a chain of component `Store`s at `OffPtr`s of the destination (the first
at the destination itself), the root `Store` becoming the chain's last; `dec.rules:123` is
`rewriteStructStore`. Each instance is validated by `GoFV.Opt.RewriteCheck.ssRel` (a `Store` of
an aggregate is the sequence of its component writes:
`GoFV.Proof.StructStore.split_mem`; refinement: `GoFV.Proof.Pass.StructStore.ss_refines`), so the
rule-level obligation is the shape `EffectRule.StructStore`. The matching order of the decompose
pass is kept (`Interp.Table.structStores` in file order); the size-0 elimination `dec.rules:10`,
which Go tries first, is not among them, so a size-0 `Store` it would remove is split and the
rewrite step no longer reproduces the pass (rejected, not unsound).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- `dec.rules:23`: `(Store {t} dst (ComplexMake real imag) mem) && t.Size() == 8 => …` -/
theorem r_dec_23_sound : EffectRule.StructStore GoFV.Rules.Generated.Dec.r_dec_23 := rfl

/-- `dec.rules:35`: `(Store {t} dst (ComplexMake real imag) mem) && t.Size() == 16 => …` -/
theorem r_dec_35_sound : EffectRule.StructStore GoFV.Rules.Generated.Dec.r_dec_35 := rfl

/-- `dec.rules:51`: `(Store dst (StringMake ptr len) mem) => …` -/
theorem r_dec_51_sound : EffectRule.StructStore GoFV.Rules.Generated.Dec.r_dec_51 := rfl

/-- `dec.rules:72`: `(Store {t} dst (SliceMake ptr len cap) mem) => …` -/
theorem r_dec_72_sound : EffectRule.StructStore GoFV.Rules.Generated.Dec.r_dec_72 := rfl

/-- `dec.rules:93`: `(Store dst (IMake itab data) mem) => …` -/
theorem r_dec_93_sound : EffectRule.StructStore GoFV.Rules.Generated.Dec.r_dec_93 := rfl

/-- `dec.rules:123`: `(Store _ (StructMake ___) _) => rewriteStructStore(v)` -/
theorem r_dec_123_sound : EffectRule.StructStore GoFV.Rules.Generated.Dec.r_dec_123 := rfl

/-- `dec.rules:129`: `(Store dst (ArrayMake1 e) mem) => (Store {e.Type} dst e mem)` -/
theorem r_dec_129_sound : EffectRule.StructStore GoFV.Rules.Generated.Dec.r_dec_129 := rfl

end GoFV.Proof.Rules
