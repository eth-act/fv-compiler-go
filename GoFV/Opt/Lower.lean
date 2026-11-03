import GoFV.Rules.Run
import GoFV.Rules.Generated.ARM64
import GoFV.Rules.Generated.ARM64latelower

/-!
# lower, late lower (`lower.go`)

`lower` = `applyRewrite(f, rewriteBlockARM64, rewriteValueARM64, removeDeadValues)`;
`late lower` = the same with `rewriteBlockARM64latelower` (no block rules) and
`rewriteValueARM64latelower` (docs/PASSES2.md, issues #388, #390, #381).
-/

namespace GoFV.Opt

open GoFV.Rules

/-- The `ARM64.rules` rules, indexed by op and block kind. -/
def lowerTable : Interp.Table := Interp.Table.ofRuleSet Generated.ARM64.ruleSet

/-- The `ARM64latelower.rules` rules, indexed by op. -/
def lateLowerTable : Interp.Table := Interp.Table.ofRuleSet Generated.ARM64latelower.ruleSet

/-- `lower`. -/
def lower : Pass := rewritePass lowerTable true

/-- `late lower`. -/
def lateLower : Pass := rewritePass lateLowerTable true

end GoFV.Opt
