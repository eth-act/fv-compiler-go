import GoFV.Opt.RewriteCheck
import GoFV.Rules.Generated.Generic

variable [GoFV.SSA.Sem.Addrs]

/-!
# Segment rules (issue #151)

`generic.rules:1833`/`:1844`/`:1857` drop a `Zero` under the `Store`s that tile it, and
`:1638`/`:1721`/`:1730` turn `SelectN [0]` of a `memclrNoHeapPointers`/`memmove` call into
`Zero`/`Move`, and `:1743` turns a `Move` from a read-only symbol whose bytes are zero into a
`Zero`, and `:1978`/`:1992`/`:2011`/`:2035` (and the `VarDef` forms `:2049`/`:2064`/`:2084`/`:2109`)
turn a `Move` of stores over a `Zero` into the same stores at the destination over a `Zero` of it
(`RewriteCheck.moveSeg?`, issue #69). They rewrite a segment of a block's memory roots (the anchor redefined in place,
clobbered values dropped, fresh `Store`s put in), whose intermediate memories differ from the
source's, so `Rule.SoundT` does not apply; the checked rewrite takes each instance out of the log
and relates the input to the function with the segment rewritten (`GoFV.Opt.RewriteCheck.segRel`;
refinement: `GoFV.Proof.Seg.seg_refines`, under `Env.MemOps` for the calls and `RoImage` for the
read-only symbols). The rule-level
obligation `EffectRule.Seg` is the shape that makes this per-instance check apply
(`RewriteCheck.segShapeOK`). The `Const32` alternatives (`r_generic_1638_2`, …) are left out: the
validator asks a 64-bit size.
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- **The obligation of a segment rule**: a `Store`, `SelectN` or `Move` rule with a built result in
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

/-- `generic.rules:1743`: `Move` from a read-only zero symbol becomes `Zero` -/
theorem r_generic_1743_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_1743 := rfl

/-- `generic.rules:1978`: `Move` of 1 `Store` over a `Zero` becomes the stores at `dst` over a `Zero` (`moveSeg?`) -/
theorem r_generic_1978_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_1978 := rfl

/-- `generic.rules:1992`: `Move` of 2 `Store`s over a `Zero` becomes the stores at `dst` over a `Zero` (`moveSeg?`) -/
theorem r_generic_1992_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_1992 := rfl

/-- `generic.rules:2011`: `Move` of 3 `Store`s over a `Zero` becomes the stores at `dst` over a `Zero` (`moveSeg?`) -/
theorem r_generic_2011_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_2011 := rfl

/-- `generic.rules:2035`: `Move` of 4 `Store`s over a `Zero` becomes the stores at `dst` over a `Zero` (`moveSeg?`) -/
theorem r_generic_2035_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_2035 := rfl

/-- `generic.rules:2049`: `Move` of a `VarDef` of 1 `Store` over a `Zero` becomes the stores at `dst` over a `Zero` (`moveSeg?`) -/
theorem r_generic_2049_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_2049 := rfl

/-- `generic.rules:2064`: `Move` of a `VarDef` of 2 `Store`s over a `Zero` becomes the stores at `dst` over a `Zero` (`moveSeg?`) -/
theorem r_generic_2064_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_2064 := rfl

/-- `generic.rules:2084`: `Move` of a `VarDef` of 3 `Store`s over a `Zero` becomes the stores at `dst` over a `Zero` (`moveSeg?`) -/
theorem r_generic_2084_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_2084 := rfl

/-- `generic.rules:2109`: `Move` of a `VarDef` of 4 `Store`s over a `Zero` becomes the stores at `dst` over a `Zero` (`moveSeg?`) -/
theorem r_generic_2109_sound : EffectRule.Seg GoFV.Rules.Generated.Generic.r_generic_2109 := rfl

/-- Non-vacuity: a value rule on `Store` without a built result (`:1005`, `=> mem`) does not have
the shape. -/
example : GoFV.Opt.RewriteCheck.segShapeOK GoFV.Rules.Generated.Generic.r_generic_1005 = false :=
  rfl

end GoFV.Proof.Rules
