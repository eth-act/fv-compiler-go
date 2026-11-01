import GoFV.Opt.RewriteCheck
import GoFV.Rules.Generated.Generic

/-!
# Segment rules (issue #151)

`generic.rules:1833`/`:1844`/`:1857` drop a `Zero` under the `Store`s that tile it, and
`:1638`/`:1721`/`:1730` turn `SelectN [0]` of a `memclrNoHeapPointers`/`memmove` call into
`Zero`/`Move`. They rewrite a segment of a block's memory roots (the anchor redefined in place,
clobbered values dropped, fresh `Store`s put in), whose intermediate memories differ from the
source's, so `Rule.SoundT` does not apply; the checked rewrite takes each instance out of the log
and relates the input to the function with the segment rewritten (`GoFV.Opt.RewriteCheck.segRel`;
refinement: `GoFV.Proof.Seg.seg_refines`, under `Env.MemOps` for the calls). The rule-level
obligation `EffectRule.Seg` is the shape that makes this per-instance check apply
(`RewriteCheck.segShapeOK`). The `Const32` alternatives (`r_generic_1638_2`, …) are left out: the
validator asks a 64-bit size.
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- **The obligation of a segment rule**: a `Store` or `SelectN` rule with a built result in
`v`'s block (`RewriteCheck.segShapeOK`); each instance is validated by `RewriteCheck.segRel`. -/
def EffectRule.Seg (r : Rule) : Prop := GoFV.Opt.RewriteCheck.segShapeOK r = true

/-- `generic.rules:1833`: two `Store`s tiling a `Zero` -/
theorem r_generic_1833_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_1833 := rfl

/-- `generic.rules:1844`: three `Store`s tiling a `Zero` -/
theorem r_generic_1844_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_1844 := rfl

/-- `generic.rules:1857`: four `Store`s tiling a `Zero` -/
theorem r_generic_1857_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_1857 := rfl

/-- `generic.rules:1638`: `memclrNoHeapPointers` (`StaticCall`) becomes `Zero` -/
theorem r_generic_1638_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_1638 := rfl

/-- `generic.rules:1721`: `memmove` (`StaticCall`, register arguments) becomes `Move` -/
theorem r_generic_1721_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_1721 := rfl

/-- `generic.rules:1730`: `memmove` (`StaticLECall`) becomes `Move` -/
theorem r_generic_1730_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_1730 := rfl

/-- Non-vacuity: a value rule on `Store` without a built result (`:1005`, `=> mem`) does not have
the shape. -/
example : GoFV.Opt.RewriteCheck.segShapeOK GoFV.Rules.Generated.Generic.r_generic_1005 = false :=
  rfl

end GoFV.Proof.Rules
