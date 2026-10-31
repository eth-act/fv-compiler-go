import GoFV.Rules.Run
import GoFV.Rules.Generated.Generic
import GoFV.Rules.Generated.Divisible
import GoFV.Rules.Generated.Divmod

/-!
# opt, middle opt, late opt, divisible, divmod (`opt.go`)

`opt` = `applyRewrite(f, rewriteBlockgeneric, rewriteValuegeneric, removeDeadValues)`, run as
`opt`, `middle opt` and `late opt` (the pass name is visible to the rules);
`divisible`/`divmod` likewise with their rule files (docs/PASSES.md, issues #7, #25).
-/

namespace GoFV.Opt

open GoFV.Rules

/-- The generic rules, indexed by op. -/
def genericTable : Interp.Table := Interp.Table.ofRuleSet Generated.Generic.ruleSet
def divisibleTable : Interp.Table := Interp.Table.ofRuleSet Generated.Divisible.ruleSet
def divmodTable : Interp.Table := Interp.Table.ofRuleSet Generated.Divmod.ruleSet

/-- `opt` (also `middle opt`, `late opt`). -/
def opt : Pass := rewritePass genericTable true

/-- `divisible`. -/
def divisible : Pass := rewritePass divisibleTable true

/-- `divmod`. -/
def divmod : Pass := rewritePass divmodTable true

end GoFV.Opt
